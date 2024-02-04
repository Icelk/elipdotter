//! Query parsing and resolving.
//!
//! This handles AND, OR, and NOT operations, as well as parentheses which are resolved before the
//! others.

use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::fmt::{self, Debug, Display};
use std::iter::Peekable;

use crate::index::{self, AssociatedOccurrence};
use crate::index::{Occurence, Provider};
use crate::proximity::ProximateMap;
use crate::{proximity, set};
use iter_set::Inclusion;
pub use parse::{parse, Options as ParseOptions};

#[derive(Debug, Clone)]
#[must_use]
/// Eq implementation doesn't care of which is left and right.
pub struct BinaryPart {
    pub left: Part,
    pub right: Part,
}
impl BinaryPart {
    pub fn new(left: Part, right: Part) -> Self {
        Self { left, right }
    }
    #[must_use]
    pub fn into_box(self) -> Box<Self> {
        Box::new(self)
    }
    /// Swaps [`Self::left`] and [`Self::right`].
    ///
    /// This does not affect [`Eq`].
    pub fn swap(&mut self) {
        std::mem::swap(&mut self.left, &mut self.right);
    }
    /// Tests the equality of the parts AND order of [`Self::left`] & [`Self::right`].
    #[must_use]
    pub fn eq_order(&self, other: &Self) -> bool {
        self.left.eq_order(&other.left) && self.right.eq_order(&other.right)
    }
}
impl PartialEq for BinaryPart {
    fn eq(&self, other: &Self) -> bool {
        (self.left == other.left && self.right == other.right)
            || (self.left == other.right && self.right == other.left)
    }
}
impl Eq for BinaryPart {}

/// A part of a [`Query`].
#[derive(PartialEq, Eq, Clone)]
#[must_use]
pub enum Part {
    And(Box<BinaryPart>),
    Or(Box<BinaryPart>),
    Not(Box<Part>),

    String(String),
}
impl Part {
    pub fn s(s: impl AsRef<str>) -> Self {
        Self::String(s.as_ref().into())
    }
    pub fn and(left: impl Into<Self>, right: impl Into<Self>) -> Self {
        Self::And(BinaryPart::new(left.into(), right.into()).into_box())
    }
    pub fn or(left: impl Into<Self>, right: impl Into<Self>) -> Self {
        Self::Or(BinaryPart::new(left.into(), right.into()).into_box())
    }
    pub fn not(not: impl Into<Self>) -> Self {
        Self::Not(Box::new(not.into()))
    }

    pub fn for_each<'a>(&'a self, f: &mut impl FnMut(&'a Part)) {
        f(self);
        match self {
            Self::And(pair) | Self::Or(pair) => {
                pair.left.for_each(f);
                pair.right.for_each(f);
            }
            Self::Not(not) => not.for_each(f),
            Self::String(_s) => {}
        }
    }
    pub fn for_each_string<'a>(&'a self, f: &mut impl FnMut(&'a str)) {
        match self {
            Self::And(pair) | Self::Or(pair) => {
                pair.left.for_each_string(f);
                pair.right.for_each_string(f);
            }
            Self::Not(not) => not.for_each_string(f),
            Self::String(s) => f(s),
        }
    }

    /// Tests the equality of the parts AND order.
    ///
    /// See [`BinaryPart`] for more details.
    ///
    /// This makes no difference to the [`Eq`] implementation if `self` is [`Self::Not`] or
    /// [`Self::String`].
    #[must_use]
    pub fn eq_order(&self, other: &Self) -> bool {
        if !self.eq(other) {
            return false;
        }
        match self {
            Self::String(_) | Self::Not(_) => true,
            Self::Or(p1) | Self::And(p1) => {
                if let Self::Or(p2) | Self::And(p2) = other {
                    p1.eq_order(p2)
                } else {
                    false
                }
            }
        }
    }
    /// Casts a generic [`Iterator`] to a [`dyn`](https://doc.rust-lang.org/std/keyword.dyn.html) one.
    ///
    /// This is a convenience function as the cast is hard inline.
    fn iter_to_box<'a, T>(iter: impl Iterator<Item = T> + 'a) -> Box<dyn Iterator<Item = T> + 'a> {
        Box::new(iter)
    }
    #[allow(clippy::type_complexity)]
    fn fn_to_box<'a, T>(
        f: impl FnMut(&'a str) -> Option<Box<dyn Iterator<Item = T> + 'a>> + 'a,
    ) -> Box<(dyn FnMut(&'a str) -> Option<Box<dyn Iterator<Item = T> + 'a>> + 'a)> {
        Box::new(f)
    }
    fn as_doc_iter<
        'a,
        'b,
        T: Ord + 'a,
        AndMI: Iterator<Item = T> + 'a,
        OrMI: Iterator<Item = T> + 'a,
    >(
        &'a self,
        mut iter: impl std::ops::DerefMut<
                Target = (impl FnMut(&'a str) -> Option<Box<dyn Iterator<Item = T> + 'a>> + ?Sized + 'a),
            > + 'b,
        and_not_modify: &impl Fn(
            Box<dyn Iterator<Item = T> + 'a>,
            Box<dyn Iterator<Item = T> + 'a>,
        ) -> Box<dyn Iterator<Item = T> + 'a>,
        and_merger: &impl Fn(
            Box<dyn Iterator<Item = T> + 'a>,
            Box<dyn Iterator<Item = T> + 'a>,
        ) -> AndMI,
        or_merger: &impl Fn(Box<dyn Iterator<Item = T> + 'a>, Box<dyn Iterator<Item = T> + 'a>) -> OrMI,
    ) -> Result<Box<dyn Iterator<Item = T> + 'a>, IterError> {
        let iter = match self {
            Self::And(pair) => match (&pair.left, &pair.right) {
                (other, Part::Not(not)) | (Part::Not(not), other) => and_not_modify(
                    other.as_doc_iter(&mut *iter, and_not_modify, and_merger, or_merger)?,
                    not.as_doc_iter(&mut *iter, and_not_modify, and_merger, or_merger)?,
                ),
                _ => Self::iter_to_box(and_merger(
                    pair.left
                        .as_doc_iter(&mut *iter, and_not_modify, and_merger, or_merger)?,
                    pair.right
                        .as_doc_iter(&mut *iter, and_not_modify, and_merger, or_merger)?,
                )),
            },
            Self::Or(pair) => Self::iter_to_box(or_merger(
                pair.left
                    .as_doc_iter(&mut *iter, and_not_modify, and_merger, or_merger)?,
                pair.right
                    .as_doc_iter(&mut *iter, and_not_modify, and_merger, or_merger)?,
            )),
            Self::Not(_) => return Err(IterError::StrayNot),
            Self::String(s) => {
                iter(s).map_or_else(|| Self::iter_to_box(std::iter::empty()), Self::iter_to_box)
            }
        };
        Ok(iter)
    }
}
impl<T: Into<String>> From<T> for Part {
    fn from(s: T) -> Self {
        Self::String(s.into())
    }
}
impl Debug for Part {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}
impl Display for Part {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_pair(f: &mut fmt::Formatter<'_>, pair: &BinaryPart, op: &str) -> fmt::Result {
            write!(f, "({} {} {})", pair.left, op, pair.right)
        }
        match self {
            Self::String(s) => f.write_str(s),
            Self::And(pair) => fmt_pair(f, pair, "AND"),
            Self::Or(pair) => fmt_pair(f, pair, "OR"),
            Self::Not(not) => write!(f, "(NOT {})", not),
        }
    }
}

/// An iterator of documents which matches a [`Query`].
#[derive(Debug)]
pub struct Documents<'a, 'b, P: Provider<'a>> {
    proximate_map: ProximateMap<'b>,
    query: &'b Query,
    provider: &'a P,
}
impl<'a, 'b, P: Provider<'a>> Documents<'a, 'b, P> {
    /// # Errors
    ///
    /// If a [`Part::Not`] isn't associated with a [`Part::And`], [`IterError::StrayNot`] is
    /// returned.
    ///
    /// This is due to a limitation of the index architecture used by this library,
    /// and almost all other search engines.
    #[allow(clippy::iter_not_returning_iterator)] // it does, within a result
    pub fn iter(&'a self) -> Result<impl Iterator<Item = index::Id> + 'a, IterError> {
        self.query.root().as_doc_iter(
            if let proximity::Algorithm::Exact = self.provider.word_proximity_algorithm() {
                Part::fn_to_box(|s| self.provider.documents_with_word(s).map(Part::iter_to_box))
            } else {
                Part::fn_to_box(|s| {
                    let list = self.proximate_map.get_panic(s);
                    Some(Part::iter_to_box(
                        crate::proximity::proximate_word_docs(self.provider, list)
                            .map(|item| item.id)
                            .collect::<BTreeSet<_>>()
                            .into_iter(),
                    ))
                })
            },
            &|i, _| i,
            &set::intersect,
            &set::union,
        )
    }
    /// The list of proximate words.
    /// This is populated on creation and used in [`Self::iter`].
    /// Using [`Self::iter`] after calling this will most likely result in a panic.
    pub fn take_proximate_map(&mut self) -> ProximateMap<'b> {
        core::mem::take(&mut self.proximate_map)
    }
}

/// A query.
///
/// This is just a root [`Part`].
///
/// Use [`mod@parse`] to create one.
/// You can also use the [`std::str::FromStr`] implementation.
#[derive(Debug, PartialEq, Eq, Clone)]
#[must_use]
pub struct Query {
    root: Part,
}
impl Query {
    fn new(root: Part) -> Self {
        Self { root }
    }
    /// Get a reference to the root node of the query.
    pub fn root(&self) -> &Part {
        &self.root
    }
    pub fn documents<'a, 'b, P: Provider<'a>>(&'b self, provider: &'a P) -> Documents<'a, 'b, P> {
        let mut proximate_map = proximity::ProximateMap::new();
        if let proximity::Algorithm::Exact = provider.word_proximity_algorithm() {
            // Do nothing, it doesn't read this.
        } else {
            self.root().for_each_string(&mut |s| {
                proximity::proximate_words(s, provider).extend_proximates(&mut proximate_map);
            });
        }
        Documents {
            proximate_map,
            query: self,
            provider,
        }
    }
    /// The `distance_threshold` is the bytes between two occurrences to consider the "same", which
    /// increases [`Hit::rating`].
    ///
    /// # Errors
    ///
    /// See [`Self::documents`].
    ///
    /// # Panics
    ///
    /// Some implementations of [`index::OccurenceProvider`] panic under certain circumstances.
    ///
    /// [`index::SimpleOccurences`], for example, panics if you haven't supplied all the necessary
    /// documents.
    #[allow(clippy::too_many_lines)]
    pub fn occurrences<'a>(
        &'a self,
        provider: &'a impl index::OccurenceProvider<'a>,
        distance_threshold: usize,
    ) -> Result<impl Iterator<Item = Hit> + 'a, IterError> {
        #[derive(Debug, Clone)]
        struct OccurenceEq(Hit);
        impl OccurenceEq {
            #[inline]
            fn new(mut occ: Occurence, word_id: u32) -> Self {
                occ.word_id = word_id;
                Self(Hit::new(occ))
            }
            #[must_use]
            fn closest(&self, other: &Self) -> (usize, AssociatedOccurrence) {
                use std::cmp::Ordering;
                let mut closest = (usize::MAX, AssociatedOccurrence::new(0, 0));
                let mut a_iter = self.0.occurrences();
                // If `associated_occurrences` has len 0, use only start.
                // Else, it'll have >=2 occurences, since the `.start()` is also taken as part of
                // the BTreeSet.
                let mut a = a_iter.next().unwrap_or_else(|| (&self.0).into());
                let mut a_start = a.start();
                let mut b_iter = other.0.occurrences();
                let mut b = b_iter.next().unwrap_or_else(|| (&other.0).into());
                let mut b_start = b.start();
                let mut one_completed = false;
                loop {
                    let dist = if a_start > b_start {
                        a_start - b_start
                    } else {
                        b_start - a_start
                    };
                    closest = std::cmp::min_by((dist, b), closest, |a, b| a.0.cmp(&b.0));
                    match a.cmp(&b) {
                        Ordering::Less => {
                            if let Some(next) = a_iter.next() {
                                a = next;
                                a_start = a.start();
                            } else if one_completed {
                                break;
                            } else {
                                one_completed = true;
                            }
                        }
                        // The words are at the same place!
                        //
                        // This is technically not reachable, but the following codes makes sense.
                        Ordering::Equal => return (0, b),
                        Ordering::Greater => {
                            if let Some(next) = b_iter.next() {
                                b = next;
                                b_start = b.start();
                            } else if one_completed {
                                break;
                            } else {
                                one_completed = true;
                            }
                        }
                    }
                }
                closest
            }
        }
        impl PartialEq for OccurenceEq {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                self.0.id().eq(&other.0.id())
            }
        }
        impl Eq for OccurenceEq {}
        impl Ord for OccurenceEq {
            #[inline]
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.0.id().cmp(&other.0.id())
            }
        }
        impl PartialOrd for OccurenceEq {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Borrow<index::Id> for OccurenceEq {
            #[inline]
            fn borrow(&self) -> &index::Id {
                &self.0.occurrence.document_id
            }
        }

        #[derive(Debug)]
        struct MergeProximate<I>
        where
            I: Iterator<Item = OccurenceEq>,
        {
            iter: Peekable<I>,
            distance_threshold: usize,
        }
        impl<I: Iterator<Item = OccurenceEq>> MergeProximate<I> {
            fn new(iter: I, distance_threshold: usize) -> Self {
                Self {
                    iter: iter.peekable(),
                    distance_threshold,
                }
            }
        }
        impl<I: Iterator<Item = OccurenceEq>> Iterator for MergeProximate<I> {
            type Item = OccurenceEq;
            fn next(&mut self) -> Option<Self::Item> {
                let mut next = self.iter.next()?;

                let peeked = match self.iter.peek() {
                    Some(peeked) => peeked,
                    None => return Some(next),
                };

                if peeked.0.id() != next.0.id() {
                    return Some(next);
                }

                // `TODO`: Similar words won't get merged - they come sequentially.
                let dist = if peeked.0.start() < next.0.start() {
                    next.0.start() - peeked.0.start()
                } else {
                    peeked.0.start() - next.0.start()
                };
                if dist > self.distance_threshold {
                    return Some(next);
                }
                *next.0.rating_mut() += 2.0;
                next.0.merge(&peeked.0);
                drop(self.next());
                Some(next)
            }
        }

        #[inline]
        fn abs_diff_occurrence(a: &OccurenceEq, b: &OccurenceEq) -> usize {
            a.0.start().abs_diff(b.0.start())
        }

        let mut word_id: u32 = 0;
        self.root()
            .as_doc_iter(
                &mut move |s| {
                    // Logic error if we wrap, but we'd need more than 4M words, and it only
                    // results in marginally worse relevance for search results and context.
                    word_id = word_id.wrapping_add(1);
                    provider.occurrences_of_word(s).map(move |iter| {
                        Part::iter_to_box(MergeProximate::new(
                            iter.map(
                                #[inline]
                                move |hit| OccurenceEq::new(hit, word_id),
                            ),
                            distance_threshold,
                        ))
                    })
                },
                &|and, not| {
                    Part::iter_to_box(
                        crate::set::progressive(
                            and,
                            not,
                            #[inline]
                            |and, not| and.0.start().cmp(&not.0.start()),
                            std::cmp::Ord::cmp,
                            Some(abs_diff_occurrence),
                        )
                        .filter_map(|inclusion| match inclusion {
                            Inclusion::Left(mut and) => {
                                *and.0.rating_mut() += 2.5;
                                Some(and)
                            }
                            Inclusion::Right(_not) => None,
                            Inclusion::Both(mut and, not) => {
                                let not_rating = not.0.rating();
                                let closest = and.closest(&OccurenceEq::new(not.0.occurrence, 0));
                                // Don't really care about precision.
                                #[allow(clippy::cast_precision_loss)]
                                let rating_decrease = 1.0 / (0.0001 * closest.0 as f32 + 0.025);
                                *and.0.rating_mut() -= rating_decrease;
                                // by decreasing the rating based on the not rating too, we remove
                                // extra when there are multiple NOTs.
                                // `TODO` apply the same filter as we do below for acceted ones for
                                // the NOT occurrences, so groups are better recognized.
                                *and.0.rating_mut() -= not_rating;
                                and.0.closest_not = Some(closest.1);
                                Some(and)
                            }
                        }),
                    )
                },
                // AND merger
                &|left, right| {
                    crate::set::progressive(
                        left,
                        right,
                        #[inline]
                        |a, b| a.0.start().cmp(&b.0.start()),
                        // Compares IDs
                        #[inline]
                        |a, b| (*a).cmp(b),
                        None,
                    )
                    .filter_map(|inclusion| match inclusion {
                        Inclusion::Both(mut a, b) => {
                            a.0.merge(&b.0);
                            Some(a)
                        }
                        _ => None,
                    })
                },
                // OR merger
                &|left, right| {
                    crate::set::progressive(
                        left,
                        right,
                        #[inline]
                        |a, b| a.0.start().cmp(&b.0.start()),
                        // Compares IDs
                        #[inline]
                        |a, b| (*a).cmp(b),
                        None,
                    )
                    .map(|inclusion| match inclusion {
                        Inclusion::Both(mut a, b) => {
                            a.0.merge(&b.0);
                            a
                        }
                        Inclusion::Left(a) | Inclusion::Right(a) => a,
                    })
                },
            )
            .map(|iter| {
                iter.map(|occ| {
                    let mut occ = occ.0;

                    let mut increase = 0.;
                    // We keep track of the closest to determine which index should be the `major`
                    // one.
                    let (mut closest, mut closest_index) = (usize::MAX, 0);

                    let mut iter = occ.occurrences();
                    let mut last = iter
                        .next()
                        .unwrap_or_else(|| AssociatedOccurrence::new(0, 0));

                    for (idx, associated_occ) in iter.enumerate() {
                        if last.word_id() != associated_occ.word_id() {
                            let dist = associated_occ.start() - last.start();
                            if dist < closest {
                                closest_index = idx;
                            }
                            closest = std::cmp::min(dist, closest);
                            // Don't really care about precision.
                            #[allow(clippy::cast_precision_loss)]
                            let rating_increase = 0.5 / (0.001 * dist as f32 + 0.1);
                            increase += rating_increase;
                        }
                        last = associated_occ;
                    }
                    *occ.rating_mut() += increase;

                    // replace `occurrence.start()` with the closest match.
                    // This requires removing the closest from the set and setting as "main"
                    // and inserting "main" to the set.
                    if closest_index != 0 {
                        let closest = occ.occurrences().nth(closest_index).unwrap();
                        occ.occurrences.remove(&closest);
                        occ.occurrences.insert((&occ.occurrence).into());
                        *occ.occurrence.start_mut() = closest.start();
                    }

                    occ
                })
            })
    }
}

/// An occurrence returned from [`Query`].
#[derive(Debug, Clone)]
pub struct Hit {
    occurrence: Occurence,

    /// [`Self::occurrence`] (if [`Self::merged`]) and all associated occurrences.
    occurrences: BTreeSet<AssociatedOccurrence>,
    /// If we have been merged. Used to tell if `self.occurrence.start()` is in the occurrences
    /// BTree. We don't do this by default to avoid an allocation.
    merged: bool,

    closest_not: Option<AssociatedOccurrence>,
}
impl Hit {
    #[inline]
    fn new(occurrence: Occurence) -> Self {
        Self {
            occurrence,
            occurrences: BTreeSet::new(),
            merged: false,
            closest_not: None,
        }
    }
    /// Get a reference to the hit's document id.
    #[must_use]
    #[inline]
    pub fn id(&self) -> index::Id {
        self.occurrence.id()
    }
    /// Get a reference to the hit's word id.
    #[must_use]
    #[inline]
    pub fn word_id(&self) -> u32 {
        self.occurrence.word_id()
    }
    /// Get a reference to the hit's document id.
    ///
    /// This might be any of the [`Self::occurrences`] if that returns any items.
    #[must_use]
    #[inline]
    pub fn start(&self) -> usize {
        self.occurrence.start()
    }
    /// Get a reference to the hit's occurrence.
    #[must_use]
    #[inline]
    pub fn occurrence(&self) -> &Occurence {
        &self.occurrence
    }
    /// Get the hit's rating.
    #[must_use]
    #[inline]
    pub fn rating(&self) -> f32 {
        self.occurrence.rating()
    }
    #[inline]
    fn rating_mut(&mut self) -> &mut f32 {
        self.occurrence.rating_mut()
    }
    /// [`Self::occurrence`] and all associated occurrences.
    #[inline]
    pub fn occurrences(&self) -> impl Iterator<Item = AssociatedOccurrence> + '_ {
        let first = if self.merged {
            None
        } else {
            Some(index::AssociatedOccurrence::new(
                self.start(),
                self.occurrence.word_id(),
            ))
        };
        first.into_iter().chain(self.occurrences.iter().copied())
    }

    /// Merges two [`Hit`]s, by adding the [`Hit::occurrences`] to our set.
    ///
    /// Must have the same [document id](Self::id()).
    fn merge(&mut self, other: &Self) {
        if self.occurrences.is_empty() {
            self.occurrences.insert((&*self).into());
        }
        for other_occ in other.occurrences() {
            self.occurrences.insert(other_occ);
        }
        self.occurrences.insert(other.into());
        self.merged = true;
    }
}
impl PartialEq for Hit {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id() && self.start() == other.start()
    }
}
impl Eq for Hit {}
impl PartialOrd for Hit {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Hit {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering::Equal;
        match self.id().cmp(&other.id()) {
            Equal => self.start().cmp(&other.start()),
            cmp => cmp,
        }
    }
}

#[derive(Debug)]
pub enum IterError {
    StrayNot,
}

/// [`Query`] parsing.
pub mod parse {
    use std::fmt::{self, Debug, Display};
    use std::str::FromStr;

    use super::{BinaryPart, Part, Query};

    impl FromStr for Query {
        type Err = Error;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            s.parse().map(Query::new)
        }
    }
    impl FromStr for Part {
        type Err = Error;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            parse(s, Options::default())
        }
    }

    /// Parse `s` with `opts`.
    ///
    /// You can also use the [`FromStr`] trait implemented by [`Query`] and [`Part`]
    /// if you don't care about the [`Options`].
    #[allow(clippy::missing_panics_doc)]
    #[allow(clippy::missing_errors_doc)]
    pub fn parse(s: &str, opts: Options) -> Result<Part, Error> {
        let mut parser = Parser::new();
        let mut opts = opts;
        let opts = &mut opts;
        let mut rest = s;

        if s.is_empty() {
            return Err(Error::InputEmpty);
        }

        loop {
            let advance = parser.next(opts, rest)?;
            rest = if let Some(rest) = rest
                .char_indices()
                .nth(advance)
                .and_then(|(pos, _)| rest.get(pos..))
            {
                rest
            } else {
                return parser.finish();
            };

            if rest.is_empty() {
                return parser.finish();
            }
        }
    }

    #[derive(Debug, PartialEq, Eq)]
    pub enum StringMarkerError {
        /// The operation must be unary.
        OperationIsBinary,
    }

    /// The parser. This is public to allow you to change it's state when making a [`Rule`].
    #[derive(Debug)]
    pub struct Parser {
        sub: Option<Box<Parser>>,
        sub_layer: usize,
        pub left: Option<Part>,
        left_group_explicit: bool,
        pub string: String,
        string_marker: Option<Op>,
        old_op: Option<Op>,
        op: Option<Op>,
    }
    impl Parser {
        fn take_string(&mut self) -> Part {
            let string = std::mem::replace(&mut self.string, String::with_capacity(8));
            let part = Part::String(crate::index::Alphanumeral::new(&string).chars().collect());
            if let Some(marker) = self.string_marker.take() {
                match marker {
                    Op::Not => Part::not(part),
                    Op::And | Op::Or => {
                        unreachable!("In `set_string_marker`, we check for binary.")
                    }
                }
            } else {
                part
            }
        }
        /// # Errors
        ///
        /// Returns an error if `op` is [`Op::binary`].
        pub fn set_string_marker(&mut self, op: Op) -> Result<(), StringMarkerError> {
            if op.binary() {
                Err(StringMarkerError::OperationIsBinary)
            } else {
                self.string_marker = Some(op);
                Ok(())
            }
        }
        #[must_use]
        pub fn string_marker(&self) -> Option<Op> {
            self.string_marker
        }
        #[allow(clippy::missing_panics_doc)]
        pub fn set_op(&mut self, op: Op) {
            if op.binary() {
                self.op = Some(op);
            } else {
                // UNWRAP: See errors note and the if statement we're in.
                self.set_string_marker(op).unwrap();
            }
        }
        /// If the parser is completely empty, with no content.
        #[must_use]
        pub fn is_empty(&self) -> bool {
            self.old_op.is_none()
                && self.op.is_none()
                && self.string_marker.is_none()
                && self.string.is_empty()
                && self.sub.is_none()
                && self.left.is_none()
        }
        // start by appending to a Part::String
        // if any things (struct) are recogniced
        // add their corresponding part (method of struct, manip the tree)
        //
        // Make sure the order is right on those rules - order of importance: NOT, AND, OR
        /// # Panics
        ///
        /// Panics if `rest.is_empty()`.
        fn next(&mut self, opts: &mut Options, rest: &str) -> Result<usize, Error> {
            if let Some(sub) = &mut self.sub {
                if rest.starts_with('(') {
                    self.sub_layer += 1;
                }
                if rest.starts_with(')') {
                    self.sub_layer -= 1;
                    if self.sub_layer == 0 {
                        let parenthesis = sub.finish()?;
                        self.finish_part(self.old_op, parenthesis);
                        self.sub = None;
                        self.left_group_explicit = true;
                        return Ok(1);
                    }
                }
                return sub.next(opts, rest);
            } else if rest.starts_with('(') {
                self.sub = Some(Box::new(Self::new()));
                self.sub_layer += 1;
                return Ok(1);
            }

            let mut advance = None;
            for rule in &mut opts.rules {
                if let Some(result) = rule.next(self, rest) {
                    assert!(result > 0, "Cannot stay on the same byte.");

                    advance = Some(result);
                }
            }
            if let Some(advance) = advance {
                if !self.string.is_empty() {
                    match (self.op, self.old_op) {
                        (Some(_), None) => {
                            self.left = Some(self.take_string());
                        }
                        (_, Some(old_op)) => {
                            let right = self.take_string();
                            self.left = Some(self.finish_op(old_op, right));
                        }
                        _ => {}
                    }
                    self.left_group_explicit = false;
                }

                if let Some(op) = self.op {
                    self.old_op = Some(op);
                    self.op = None;
                }

                return Ok(advance);
            }
            let c = rest.chars().next().unwrap();
            if c.is_alphanumeric() {
                self.string.push(c);
            }
            Ok(1)
        }
        fn finish_part(&mut self, op: Option<Op>, mut right: Part) {
            if let Some(marker) = self.string_marker.take() {
                match marker {
                    Op::Not => right = Part::not(right),
                    Op::And | Op::Or => {
                        unreachable!("In `set_string_marker`, we check for binary.")
                    }
                }
            }
            if let Some(op) = op {
                self.left = Some(self.finish_op(op, right));
            } else {
                self.left = Some(right);
            }
        }
        fn finish_op(&mut self, op: Op, mut right: Part) -> Part {
            if let Op::And | Op::Or = op {
                if self.left.is_none() {
                    return right;
                }
            }
            match op {
                Op::And => {
                    // UNWRAP: See if statement in top of fn
                    let left = self.left.take().unwrap();

                    if let Part::Or(mut pair) = left {
                        if self.left_group_explicit {
                            Part::And(BinaryPart::new(Part::Or(pair), right).into_box())
                        } else {
                            std::mem::swap(&mut right, &mut pair.left);
                            pair.swap();
                            let and = Part::And(pair);
                            // We swapped the left part of the pair to `right`.
                            let or = right;
                            Part::or(or, and)
                        }
                    } else {
                        Part::And(BinaryPart::new(left, right).into_box())
                    }
                }
                Op::Or => {
                    // UNWRAP: See if statement in top of fn
                    let left = self.left.take().unwrap();
                    Part::Or(BinaryPart::new(left, right).into_box())
                }
                Op::Not => Part::Not(Box::new(right)),
            }
        }
        fn finish(&mut self) -> Result<Part, Error> {
            if !self.string.is_empty() {
                let right = self.take_string();
                self.finish_part(self.old_op, right);
            }
            self.left.take().ok_or_else(|| {
                if self.is_empty() {
                    Error::InputEmpty
                } else {
                    Error::NotEnoughArguments
                }
            })
        }
        fn new() -> Self {
            Self {
                sub: None,
                sub_layer: 0,
                left: None,
                left_group_explicit: false,
                string: String::with_capacity(8),
                string_marker: None,
                old_op: None,
                op: None,
            }
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub enum Op {
        And,
        Or,
        Not,
    }
    impl Op {
        #[must_use]
        pub fn binary(&self) -> bool {
            matches!(self, Self::And | Self::Or)
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Error {
        InputEmpty,
        /// Operation took more arguments than what was supplied.
        NotEnoughArguments,
        UnexpectedParentheses,
    }
    impl Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::InputEmpty => f.write_str("input empty"),
                Self::NotEnoughArguments => f.write_str(
                    "logic operation got too few arguments (missing word after AND or OR?)",
                ),
                Self::UnexpectedParentheses => f.write_str("parentheses in an unexpected place"),
            }
        }
    }

    /// Same as [`char::is_ascii_whitespace`], but including `\u{a0}`, non-breaking space.
    #[must_use]
    pub fn is_whitespace(c: char) -> bool {
        c.is_ascii_whitespace() || c == '\u{a0}'
    }

    /// Options to [`parse`]. Here, you can add your own formatting rules, on top of the default
    /// rules.
    #[derive(Debug)]
    #[must_use]
    pub struct Options {
        rules: Vec<Box<dyn Rule>>,
    }
    impl Options {
        /// Crates a new, empty, set of options.
        /// The order of [`Self::insert`] matters a lot.
        ///
        /// [`Self::populate_and_space`] should definitely be last.
        ///
        /// See [`crate::literal_rule!`] for an example.
        pub fn new() -> Self {
            Self { rules: Vec::new() }
        }
        pub fn insert<R: 'static + Rule>(mut self, rule: R) -> Self {
            self.rules.push(Box::new(rule));
            self
        }
        pub fn populate_literals(self) -> Self {
            self.insert(NotLiteral::default())
                .insert(AndLiteral::default())
                .insert(OrLiteral::default())
        }
        pub fn populate_not(self) -> Self {
            self.insert(DashNot::default()).insert(BangNot::default())
        }
        pub fn populate_and_space(self) -> Self {
            self.insert(AndSpace::default())
        }
    }
    impl Default for Options {
        fn default() -> Self {
            Self::new()
                .populate_literals()
                .populate_not()
                .populate_and_space()
        }
    }
    pub trait Rule: Debug {
        /// # Returns
        ///
        /// If the match is successful, make changes to the `parser` (e.g. [`Parser::set_op`])
        /// and return [`Some`] with the number of steps to step forward (length of operator).
        #[must_use]
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize>;
    }

    #[derive(Debug, Default)]
    pub struct AndSpace {
        last_was_other_op: bool,
    }
    impl Rule for AndSpace {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            if parser.string_marker().is_some() && parser.string.is_empty() {
                return None;
            }
            if parser.is_empty() {
                return None;
            }
            if !self.last_was_other_op {
                self.last_was_other_op = parser.op.is_some();
                if self.last_was_other_op {
                    return None;
                }
            }
            let c = rest.chars().next().unwrap();
            if self.last_was_other_op {
                if is_whitespace(c) || c == '-' {
                    None
                } else {
                    self.last_was_other_op = false;
                    None
                }
            } else if is_whitespace(c) || c == '-' {
                parser.op = Some(Op::And);
                Some(1)
            } else {
                None
            }
        }
    }

    /// Used in [parsing](self).
    ///
    /// # Examples
    ///
    /// See [`crate::literal_rule!`] and [`crate::not_prefix!`].
    ///
    /// ```
    /// use elipdotter::*;
    /// use elipdotter::query::Part;
    /// use elipdotter::query::parse::LiteralRule;
    /// generate_rule!(EllerLiteral, LiteralRule, LiteralRule::new("eller", query::parse::Op::Or));
    /// let opts = elipdotter::query::ParseOptions::new().populate_literals().insert(EllerLiteral::default()).populate_not().populate_and_space();
    /// let part = elipdotter::query::parse("elipdotter eller search", opts).unwrap();
    /// assert_eq!(part, Part::or("elipdotter", "search"));
    /// ```
    #[macro_export]
    macro_rules! generate_rule {
        ($name: ident, $struct: path, $new: expr) => {
            #[derive(Debug)]
            #[must_use]
            pub struct $name($struct);
            impl $name {
                pub fn new() -> Self {
                    Self($new)
                }
            }
            impl Default for $name {
                fn default() -> Self {
                    Self::new()
                }
            }
            impl $crate::query::parse::Rule for $name {
                fn next(
                    &mut self,
                    parser: &mut $crate::query::parse::Parser,
                    rest: &str,
                ) -> Option<usize> {
                    self.0.next(parser, rest)
                }
            }
        };
    }

    #[derive(Debug)]
    #[must_use]
    pub struct LiteralRule {
        literal: &'static str,
        op: Op,
        last_was_space: bool,
    }
    impl LiteralRule {
        /// Matches the `literal` with [`Op`].
        ///
        /// Will exit if nothing was detected before and this is a binary operation.
        pub fn new(literal: &'static str, op: Op) -> Self {
            Self {
                literal,
                op,
                last_was_space: true,
            }
        }
    }
    impl Rule for LiteralRule {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            if self.op.binary() && parser.string.is_empty() && parser.left.is_none() {
                self.last_was_space = rest.chars().next().map_or(false, is_whitespace);
                return None;
            }
            let rule = if self.last_was_space
                && rest
                    .get(0..self.literal.len())
                    .map_or(false, |rest| rest.eq_ignore_ascii_case(self.literal))
                && rest
                    .chars()
                    .nth(self.literal.len())
                    .map_or(false, is_whitespace)
            {
                parser.set_op(self.op);
                Some(self.literal.len())
            } else {
                None
            };

            self.last_was_space = rest.chars().next().map_or(false, is_whitespace);

            rule
        }
    }

    /// Used in [parsing](self).
    ///
    /// # Examples
    ///
    /// ```
    /// use elipdotter::*;
    /// use elipdotter::query::Part;
    /// literal_rule!(EllerLiteral, "eller", query::parse::Op::Or);
    /// let opts = elipdotter::query::ParseOptions::new().populate_literals().insert(EllerLiteral::default()).populate_not().populate_and_space();
    /// let part = elipdotter::query::parse("elipdotter eller search", opts).unwrap();
    /// assert_eq!(part, Part::or("elipdotter", "search"));
    /// ```
    #[macro_export]
    macro_rules! literal_rule {
        ($name: ident, $literal: expr, $op: expr) => {
            $crate::generate_rule!(
                $name,
                $crate::query::parse::LiteralRule,
                $crate::query::parse::LiteralRule::new($literal, $op)
            );
        };
    }

    literal_rule!(AndLiteral, "and", Op::And);
    literal_rule!(OrLiteral, "or", Op::Or);
    literal_rule!(NotLiteral, "not", Op::Not);

    #[derive(Debug)]
    #[must_use]
    pub struct NotPrefix {
        prefix: &'static str,
        last_was_space: bool,
    }
    impl NotPrefix {
        pub fn new(prefix: &'static str) -> Self {
            Self {
                prefix,
                last_was_space: true,
            }
        }
    }
    impl Rule for NotPrefix {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            let rule = if self.last_was_space && rest.starts_with(self.prefix) {
                parser.set_op(Op::Not);
                Some(self.prefix.len())
            } else {
                None
            };

            self.last_was_space = rest.chars().next().map_or(false, is_whitespace);

            rule
        }
    }

    /// Used in [parsing](self).
    ///
    /// # Examples
    ///
    /// ```
    /// use elipdotter::*;
    /// use elipdotter::query::Part;
    /// not_prefix!(HyphenNot, "-");
    /// let opts = elipdotter::query::ParseOptions::default().insert(HyphenNot::default());
    /// let part = elipdotter::query::parse("elipdotter -search", opts).unwrap();
    /// assert_eq!(part, Part::and("elipdotter", Part::not("search")));
    /// ```
    #[macro_export]
    macro_rules! not_prefix {
        ($name: ident, $prefix: expr) => {
            $crate::generate_rule!(
                $name,
                $crate::query::parse::NotPrefix,
                $crate::query::parse::NotPrefix::new($prefix)
            );
        };
    }
    not_prefix!(DashNot, "-");
    not_prefix!(BangNot, "!");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parses `s` with [`ParseOptions::default`].
    fn s(s: &str) -> Part {
        match parse(s, ParseOptions::default()) {
            Ok(p) => p,
            Err(err) => {
                panic!("Failed to parse '{}', {:?}", s, err);
            }
        }
    }

    #[test]
    fn binary_swap_eq() {
        let part = s("icelk kvarn");
        let mut swapped = part.clone();
        if let Part::And(pair) = &mut swapped {
            pair.swap();
        } else {
            panic!("Isn't Add.");
        }
        assert_eq!(part, swapped);
    }

    #[test]
    fn parse_and() {
        let input = "icelk kvarn";
        let part = s(input);
        assert_eq!(part, Part::and("icelk", "kvarn"));
    }
    #[test]
    fn parse_and_chain() {
        let input = "icelk kvarn web server";
        let part = s(input);
        assert_eq!(
            part,
            Part::and(Part::and(Part::and("icelk", "kvarn"), "web"), "server")
        );
    }
    #[test]
    fn parse_plain_not() {
        let part = s("not icelk");
        assert_eq!(part, Part::not("icelk"));
    }
    #[test]
    fn parse_plain_or() {
        let p = s("or");
        assert_eq!(p, Part::s("or"));
        let p = s("for me");
        assert_eq!(p, Part::and("for", "me"));
    }
    #[test]
    fn parse_empty() {
        assert_eq!(
            parse("", ParseOptions::default()).unwrap_err(),
            parse::Error::InputEmpty
        );
    }
    #[test]
    fn parse_without_ops() {
        assert_eq!(s("icelk"), Part::s("icelk"),);
    }
    #[test]
    fn parse_and_before_or() {
        let i1 = "icelk and kvarn or agde";
        let i2 = "agde or icelk and kvarn";
        let p1 = s(i1);
        let p2 = s(i2);

        let correct = Part::or(Part::and("icelk", "kvarn"), "agde");
        assert_eq!(p1, correct);
        assert!(p1.eq_order(&correct));
        assert_eq!(p2, correct);
        assert!(!p2.eq_order(&correct));
        assert_eq!(p1, p2);

        let implicit = "icelk kvarn or agde";
        let p_impl = s(implicit);

        assert_eq!(p_impl, p1);
    }
    #[test]
    fn parse_parentheses_or() {
        let p1 = s("(icelk or kvarn) and code");
        let p2 = s("code (kvarn or icelk) ");

        let correct = Part::and(Part::or("icelk", "kvarn"), "code");

        assert_eq!(p1, correct);
        assert!(p1.eq_order(&correct));
        assert_eq!(p2, correct);
        assert!(!p2.eq_order(&correct));
        assert_eq!(p1, p2);
    }
    #[test]
    fn parse_parentheses_and() {
        let p = s(" (icelk or iselk)  (kvarn or agde)))");
        assert_eq!(
            p,
            Part::and(Part::or("icelk", "iselk"), Part::or("kvarn", "agde"))
        );
    }
    #[test]
    fn parse_parentheses_and_not() {
        let p = s("icelk -(agde or kvarn)");
        assert_eq!(p, Part::and("icelk", Part::not(Part::or("kvarn", "agde"))));

        let p = s("icelk - (agde or kvarn)");
        assert_eq!(p, Part::and("icelk", Part::not(Part::or("kvarn", "agde"))));
    }
    #[test]
    fn parse_not() {
        let p = s("not");
        assert_eq!(p, Part::s("not"));
        assert_eq!(
            parse("not ", ParseOptions::default()).unwrap_err(),
            parse::Error::NotEnoughArguments
        );
    }
    #[test]
    fn parse_space() {
        assert_eq!(
            parse(" ", ParseOptions::default()).unwrap_err(),
            parse::Error::InputEmpty
        );
    }
    #[test]
    fn parse_parentheses_space() {
        assert_eq!(
            parse(" (  ) ", ParseOptions::default()).unwrap_err(),
            parse::Error::InputEmpty,
        );
    }
    #[test]
    fn parse_binary_one_arg() {
        let p = s("or icelk");
        assert_eq!(p, Part::and("or", "icelk"));
    }
    #[test]
    fn parse_parentheses_binary_one_arg() {
        let p = s("(or (icelk))");
        assert_eq!(p, Part::and("or", "icelk"));
    }
    #[test]
    fn parse_operation_order() {
        let p = s("icelk and not kvarn or agde");
        assert_eq!(p, Part::or(Part::and("icelk", Part::not("kvarn")), "agde"));

        let p = s("icelk or not kvarn or agde");
        assert_eq!(p, Part::or(Part::or("icelk", Part::not("kvarn")), "agde"));

        let p = s("agde not sync or icelk and not kvarn or agde");
        assert_eq!(
            p,
            Part::or(
                Part::or(
                    Part::and("agde", Part::not("sync")),
                    Part::and("icelk", Part::not("kvarn"))
                ),
                "agde"
            )
        );
    }
    #[test]
    fn parse_prefix_not() {
        assert_eq!(s("icelk !kvarn"), s("icelk -kvarn"));
        assert_eq!(s("icelk !kvarn"), Part::and("icelk", Part::not("kvarn")));
        assert_eq!(
            s("elipdotter -search"),
            Part::and("elipdotter", Part::not("search"))
        );
    }
    #[test]
    fn parse_non_alphanumeral() {
        assert_eq!(s("icelk.dev"), Part::s("icelkdev"));
        assert_eq!(
            s("next-generation kvarn"),
            Part::and(Part::and("next", "generation"), "kvarn")
        );
    }

    fn p_disp_match(string: &str) {
        let p = s(string);
        assert_eq!(p, s(&p.to_string()));
    }
    #[test]
    fn parse_display() {
        p_disp_match("agde not sync or icelk and not kvarn or agde");
        p_disp_match(" ( kvarn ) icelk ");
        p_disp_match(" (icelk or iselk)  (kvarn or agde)))");
        p_disp_match("(or (icelk))");
    }
}
