//! The index (lookup table of words) lives here.
//! The trait [`Provider`] (and [`OccurenceProvider`])
//! enables multiple types of indices to be defined.
//!
//! The only one (for now) is [`Simple`]. That stores a list of all the documents
//! which contains each word in the input data (e.g. web pages). It then fetches those documents
//! again and finds occurrences within those.
//!
//! ---
//!
//! The [`DocumentMap`] makes it performant to get the document ID from name and vice versa.

use std::cmp;
use std::collections::{btree_map, btree_set, BTreeMap, BTreeSet, HashMap};
use std::fmt::{Debug, Display};
use std::iter::{Copied, Map};
use std::sync::{Arc, Mutex};

use crate::proximity;

/// Id of a document.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct Id(u64);
impl Id {
    fn new(id: u64) -> Self {
        Self(id)
    }
    #[must_use]
    pub fn inner(self) -> u64 {
        self.0
    }
}

/// An occurrence of [`crate::Query`].
#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub struct Occurence {
    start: usize,
    pub(crate) document_id: Id,
    pub(crate) word_id: u32,
    rating: f32,
}
impl Occurence {
    #[inline]
    fn new(pos: usize, document_id: Id, word_id: u32) -> Self {
        Self {
            start: pos,
            document_id,
            word_id,
            rating: 0.0,
        }
    }
    #[must_use]
    #[inline]
    pub fn start(&self) -> usize {
        self.start
    }
    #[must_use]
    #[inline]
    pub fn id(&self) -> Id {
        self.document_id
    }
    #[must_use]
    #[inline]
    pub fn word_id(&self) -> u32 {
        self.word_id
    }
    #[must_use]
    #[inline]
    pub fn rating(&self) -> f32 {
        self.rating
    }
    #[inline]
    pub(crate) fn rating_mut(&mut self) -> &mut f32 {
        &mut self.rating
    }
    #[inline]
    pub(crate) fn start_mut(&mut self) -> &mut usize {
        &mut self.start
    }
}
/// If [`Occurence`] is part of an AND, these can be associated to tell where the other parts of
/// the AND chain are.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct AssociatedOccurrence {
    start: usize,
    word_id: u32,
}
impl From<&crate::Hit> for AssociatedOccurrence {
    #[inline]
    fn from(hit: &crate::Hit) -> Self {
        Self {
            start: hit.start(),
            word_id: hit.word_id(),
        }
    }
}
impl From<&Occurence> for AssociatedOccurrence {
    #[inline]
    fn from(occ: &Occurence) -> Self {
        Self {
            start: occ.start(),
            word_id: occ.word_id(),
        }
    }
}
impl AssociatedOccurrence {
    pub(crate) fn new(start: usize, word_id: u32) -> Self {
        Self { start, word_id }
    }
    /// Get the associated occurrence's start.
    #[must_use]
    #[inline]
    pub fn start(&self) -> usize {
        self.start
    }
    /// Get the associated occurrence's word id.
    #[must_use]
    #[inline]
    pub fn word_id(&self) -> u32 {
        self.word_id
    }
}

/// Wrapper for representing `T` as only containing alphanumeric characters.
///
/// The [`Eq`] and [`Ord`] implementations discard any eventual non-alphanumeric characters.
///
/// Can with benefits be used with [`StrPtr`].
#[derive(Clone, Hash)]
#[repr(transparent)]
pub struct Alphanumeral<T: ?Sized>(T);
impl<T> Alphanumeral<T> {
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn new(s: T) -> Self {
        Self(s)
    }
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn owned(&self) -> Alphanumeral<T::Owned>
    where
        T: ToOwned + AsRef<str>,
    {
        Alphanumeral::new(self.0.to_owned())
    }
}
impl<T: AsRef<str>> From<T> for Alphanumeral<T> {
    fn from(v: T) -> Self {
        Self::new(v)
    }
}
impl<T: AsRef<str>> Alphanumeral<T> {
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn chars(&self) -> impl Iterator<Item = char> + Clone + '_ {
        self.0
            .as_ref()
            .chars()
            .filter(|c: &char| c.is_alphanumeric())
            .flat_map(char::to_lowercase)
    }
}
impl<T: AsRef<str>> AsRef<str> for Alphanumeral<T> {
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}
impl<T1: AsRef<str>, T2: AsRef<str>> PartialEq<T1> for Alphanumeral<T2> {
    fn eq(&self, other: &T1) -> bool {
        self.chars().eq(Alphanumeral::new(other).chars())
    }
}
impl<T: AsRef<str>> Eq for Alphanumeral<T> {}
impl<T: AsRef<str>> PartialOrd for Alphanumeral<T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: AsRef<str>> Ord for Alphanumeral<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.chars().cmp(Alphanumeral::new(other).chars())
    }
}
impl<T: AsRef<str>> Debug for Alphanumeral<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.chars().collect::<String>())
    }
}
impl<T: AsRef<str>> Display for Alphanumeral<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.chars().collect::<String>())
    }
}

/// Needed to index a [custom struct](Alphanumeral) in maps.
/// We have to have the same type, so this acts as both the borrowed and owned.
pub struct StrPtr {
    s: *const str,
    /// drop if it's owned
    owned: bool,
}
impl StrPtr {
    /// # Safety
    ///
    /// `s` must be valid for the lifetime of this object.
    ///
    /// If `drop` is true, we must also own `s`.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    unsafe fn new(s: &str, drop: bool) -> Self {
        Self { s, owned: drop }
    }
    /// # Safety
    ///
    /// `s` must be valid for the lifetime of this object.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    unsafe fn sref<'a>(s: &'a str) -> Self
    where
        Self: 'a,
    {
        // Since `drop` is false, we don't care about ownership.
        Self::new(s, false)
    }
    #[allow(clippy::inline_always)]
    #[inline(always)]
    fn owned(s: impl Into<Box<str>>) -> Self {
        let s = std::mem::ManuallyDrop::new(s.into());
        // SAFETY: Since we have the ownership and used `ManuallyDrop`,
        // the memory will never drop.
        // We have to drop it, and it's valid until we do so.
        unsafe { Self::new(&*s, true) }
    }
    #[allow(clippy::inline_always)]
    #[inline(always)]
    fn as_mut(&self) -> *mut str {
        self.s as *mut _
    }
}
impl Drop for StrPtr {
    fn drop(&mut self) {
        if self.owned {
            // SAFETY: Upheld by caller.
            unsafe { (self.as_mut()).drop_in_place() }
        }
    }
}
impl AsRef<str> for StrPtr {
    #[allow(clippy::inline_always)]
    #[inline(always)]
    fn as_ref(&self) -> &str {
        // SAFETY: Guaranteed by caller of [`Self::new`] that the string is valid for the lifetime
        // of this struct.
        unsafe { &*self.s }
    }
}
impl Debug for StrPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.as_ref(), f)
    }
}
impl Display for StrPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.as_ref(), f)
    }
}
impl ToOwned for StrPtr {
    type Owned = Self;
    fn to_owned(&self) -> Self::Owned {
        let s = self.as_ref().to_owned();
        Self::owned(s)
    }
}
unsafe impl Send for StrPtr {}
unsafe impl Sync for StrPtr {}

pub(crate) type AlphanumRef = Alphanumeral<StrPtr>;

/// Map of documents and their [`Id`]s to quickly get name from id and vice versa.
#[derive(Debug)]
#[must_use]
pub struct DocumentMap {
    name_to_id: HashMap<String, Id>,
    id_to_name: BTreeMap<Id, String>,
}
impl DocumentMap {
    pub fn new() -> Self {
        Self {
            name_to_id: HashMap::new(),
            id_to_name: BTreeMap::new(),
        }
    }
    #[allow(clippy::missing_panics_doc)]
    pub fn reserve_id(&mut self, name: impl Into<String> + AsRef<str>) -> Id {
        if let Some(id) = self.get_id(name.as_ref()) {
            return id;
        }

        let name = name.into();

        let id = self.get_first();

        self.name_to_id.insert(name.clone(), id);
        let old_doc = self.id_to_name.insert(id, name);
        assert_eq!(old_doc, None);
        id
    }
    /// Alternatively, [`Self::reserve_id`] and then drop the lock, go to a different thread, and
    /// make a new [`Simple`]. [`Simple::digest_document`], then [`Simple::ingest`] the
    /// second index into the first.
    pub fn insert<'a>(
        &mut self,
        name: impl Into<String> + AsRef<str>,
        content: &str,
        provider: &mut impl Provider<'a>,
    ) {
        let id = self.reserve_id(name);
        provider.digest_document(id, content);
    }
    /// Get first unused [`Id`].
    fn get_first(&self) -> Id {
        if self.id_to_name.is_empty() {
            return Id::new(0);
        }
        let mut last = 0;
        for id in self.id_to_name.keys() {
            if id.inner() != last && id.inner() != last + 1 {
                return Id::new(last + 1);
            }
            last = id.inner();
        }
        Id::new(last + 1)
    }
    /// O(1)
    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.get_id(name).is_some()
    }
    /// O(1)
    #[must_use]
    pub fn get_id(&self, name: &str) -> Option<Id> {
        self.name_to_id.get(name).copied()
    }
    /// O(log n)
    ///
    /// But since this is a BTree, this is often faster than O(1) in a hash map,
    /// if we assume you have < 10_000 documents.
    #[must_use]
    pub fn get_name(&self, id: Id) -> Option<&str> {
        self.id_to_name.get(&id).map(|s| &**s)
    }

    // Option:
    //  If we have UUIDs instead, we can just remove the Id from `self`,
    //  as any attempts to resolve that into a path will fail.
    #[allow(clippy::missing_panics_doc)]
    pub fn force_remove<'a>(&mut self, document: Id, provider: &mut impl Provider<'a>) {
        let previous = if let Some(prev) = self.id_to_name.remove(&document) {
            prev
        } else {
            return;
        };
        let previous = self.name_to_id.remove(&previous);
        assert_eq!(previous, Some(document));

        provider.remove_document(document);
    }
}

impl Default for DocumentMap {
    fn default() -> Self {
        Self::new()
    }
}

/// [`Eq`] isn't implemented as you'd probably want to check which document it belongs to as well.
#[derive(Debug, Clone)]
pub struct WordOccurrence {
    pos: usize,
}
impl WordOccurrence {
    /// Get the occurrence of the word's position.
    #[must_use]
    pub fn position(&self) -> usize {
        self.pos
    }
}
/// Returns the next valid UTF-8 character.
#[must_use]
pub fn next_char(c: char) -> char {
    let mut int = c as u32;
    let max = char::MAX as u32;
    // Checking the Rust source, all u32 below [`char::MAX`] and not between the range specified
    // below are OK, so the loop here shouldn't do anything.
    // Keeping it just in case of an API change, but since this is unicode, that's highly unlikely.
    loop {
        int += 1;
        if (0xD800..=0xDFFF).contains(&int) {
            int = 0xE000;
        }
        if let Some(c) = char::from_u32(int) {
            return c;
        }
        if int >= max {
            return c;
        }
    }
}
/// Allows to insert words and remove occurrences from documents.
pub trait Provider<'a> {
    type DocumentIter: Iterator<Item = Id> + ExactSizeIterator + 'a;
    type WordIter: Iterator<Item = &'a Arc<AlphanumRef>> + 'a;
    type WordFilteredIter: Iterator<Item = &'a Arc<AlphanumRef>> + 'a;

    /// The implementation should convert `word` to lower-case and remove any hyphen `-`.
    ///
    /// [`Alphanumeral`] can be used for this purpose.
    fn insert_word(&mut self, word: impl AsRef<str>, document: Id, index: usize);
    /// Removes all registered occurrences of `document` from all words.
    fn remove_document(&mut self, document: Id);
    /// If `document` contains at least one occurrence of `word`.
    fn contains_word(&self, word: impl AsRef<str>, document: Id) -> bool;
    fn documents_with_word(&'a self, word: impl AsRef<str>) -> Option<Self::DocumentIter>;
    /// Estimate of the number of bytes this index uses in memory,
    /// specifically the heap.
    ///
    /// This assumes you're on a 64-bit architecture. Else, you can expect the size to be half, as
    /// most of what's stored in an index is pointers to data.
    ///
    /// This should not be relied on. Rather, it's a *hint*.
    fn size(&self) -> usize;

    fn word_count_upper_limit(&self) -> usize;
    /// The limit of [`Self::word_count_upper_limit`] where [`Self::words_starting_with`] is used
    /// instead of [`Self::words`].
    fn word_count_limit(&self) -> usize;
    fn words(&'a self) -> Self::WordIter;
    fn words_starting_with(&'a self, c: char) -> Self::WordFilteredIter;

    fn word_proximity_threshold(&self) -> f32;
    fn word_proximity_algorithm(&self) -> proximity::Algorithm;

    /// Only adds words which are alphanumeric.
    fn digest_document(&mut self, id: Id, content: &str) {
        for item in SplitNonAlphanumeric::new(content) {
            let word = item.word();
            let index = item.index();
            if word.is_empty() {
                continue;
            }
            // Word must be alphanumeric to be added.
            // Words with hyphens are also accepted.
            if word.contains(|c: char| !c.is_alphanumeric() && c != '-') {
                continue;
            }

            self.insert_word(word, id, index);
        }
    }
}
pub trait OccurenceProvider<'a> {
    type Iter: Iterator<Item = Occurence> + 'a;
    ///
    /// `word_count_limit` is the limit where only words starting with the first [`char`] of `word`
    /// will be checked for proximity.
    fn occurrences_of_word(&'a self, word: &'a str) -> Option<Self::Iter>;
}

#[derive(Debug, Clone)]
enum SplitItem<'a> {
    /// A word was found
    Word { word: &'a str, index: usize },
    /// A hyphen-separated word was found.
    /// This can be treated as **one** word and be added, which improves search results.
    ///
    /// Adding this makes query `nextgen` match text `next-gen`.
    /// For some magical reason, the [`crate::proximity`] already provided query `generation`
    /// matching for `nextgenerationnext`, even though it's in the middle of a string.
    Hyphen {
        /// The word with the hyphen still in it.
        word: &'a str,
        /// Index of the start of the word in the original string.
        index: usize,
    },
}
impl<'a> SplitItem<'a> {
    #[inline]
    fn word(&self) -> &'a str {
        match self {
            Self::Word { word, index: _ } | Self::Hyphen { word, index: _ } => word,
        }
    }
    #[inline]
    fn index(&self) -> usize {
        match self {
            Self::Word { word: _, index } | Self::Hyphen { word: _, index } => *index,
        }
    }
}
#[derive(Debug)]
struct SplitNonAlphanumeric<'a> {
    s: &'a str,
    start: usize,
    hyphen_start: usize,
    hyphen_second_word: bool,
}
impl<'a> SplitNonAlphanumeric<'a> {
    fn new(s: &'a str) -> Self {
        Self {
            s,
            start: 0,
            hyphen_start: 0,
            hyphen_second_word: false,
        }
    }
}
impl<'a> Iterator for SplitNonAlphanumeric<'a> {
    type Item = SplitItem<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let mut iter = self.s[self.start..].char_indices();
        // Not for because we need `iter.next()` below.
        while let Some((pos, c)) = iter.next() {
            if !c.is_alphanumeric() {
                if self.hyphen_second_word {
                    let hyphen_word = &self.s[self.hyphen_start..self.start + pos];
                    self.hyphen_second_word = false;
                    // When the caller calls `next` again, we start over at the beginning of this
                    // word, since we didn't change `self.start` before returning.
                    return Some(SplitItem::Hyphen {
                        word: hyphen_word,
                        index: self.hyphen_start,
                    });
                }
                if c == '-' {
                    self.hyphen_start = self.start;
                    self.hyphen_second_word = true;
                }
                let old_start = self.start;
                self.start = self
                    .start
                    .saturating_add(iter.next().map_or(c.len_utf8(), |(pos, _)| pos));
                return Some(SplitItem::Word {
                    index: old_start,
                    word: self.s.get(old_start..old_start + pos).unwrap(),
                });
            }
        }
        let s = self.s.get(self.start..).unwrap();
        if !s.is_empty() {
            self.start += s.len();
            return Some(SplitItem::Word {
                index: self.start,
                word: s,
            });
        }
        None
    }
}
#[derive(Debug)]
enum ProximateListOrSingle<'a> {
    Single(&'a str),
    List(&'a proximity::ProximateList),
}
impl<'a> ProximateListOrSingle<'a> {
    #[allow(clippy::inline_always)]
    #[inline(always)]
    fn get(&self, word: &AlphanumRef) -> Option<f32> {
        match self {
            Self::Single(single) => {
                // SAFETY: We only use it in this scope.
                let str_ptr = unsafe { StrPtr::sref(single) };
                if word == &Alphanumeral::new(str_ptr) {
                    Some(1.0)
                } else {
                    None
                }
            }
            Self::List(list) => list.words.get(word).copied(),
        }
    }
}

#[derive(Debug)]
#[must_use]
pub struct SimpleDocMap {
    /// We need the order of documents to be sorted, as the sorted iterators relies on that.
    docs: BTreeSet<Id>,
}
impl SimpleDocMap {
    pub fn new() -> Self {
        Self {
            docs: BTreeSet::new(),
        }
    }

    pub fn insert(&mut self, document: Id) {
        self.docs.insert(document);
    }
    pub fn remove(&mut self, document: Id) {
        self.docs.remove(&document);
    }
    #[must_use]
    pub fn contains(&self, document: Id) -> bool {
        self.docs.contains(&document)
    }
    pub fn documents(&self) -> Copied<btree_set::Iter<'_, Id>> {
        self.docs.iter().copied()
    }
}
impl Default for SimpleDocMap {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
#[must_use]
pub struct Simple {
    words: BTreeMap<Arc<AlphanumRef>, SimpleDocMap>,

    proximity_threshold: f32,
    proximity_algo: proximity::Algorithm,
    word_count_limit: usize,
}
impl Simple {
    /// `proximity_threshold` is the threshold where alike words are also accepted.
    /// It uses the range [0..1], where values nearer 0 allow more words.
    /// The default is `0.9`.
    ///
    /// `proximity_threshold` is the algorithm used for proximity checking of words.
    ///
    /// `word_count_limit` is the number of words in this index where only words with the first
    /// character is used for approximate matching.
    /// Default is `2_500`.
    pub fn new(
        proximity_threshold: f32,
        proximity_algorithm: proximity::Algorithm,
        word_count_limit: usize,
    ) -> Self {
        Self {
            words: BTreeMap::new(),
            proximity_threshold,
            proximity_algo: proximity_algorithm,
            word_count_limit,
        }
    }
    /// Merges `other` with `self`.
    pub fn ingest(&mut self, other: Self) {
        for (word, docs) in other.words {
            if let Some(my_docs) = self.words.get_mut(&word) {
                for doc in docs.documents() {
                    my_docs.insert(doc);
                }
            } else {
                self.words.insert(word, docs);
            }
        }
    }
}
/// [`Self::new`] with `proximity_threshold` set to `0.85`.
impl Default for Simple {
    fn default() -> Self {
        Self::new(0.85, proximity::Algorithm::Hamming, 2_500)
    }
}
type FirstTy<'a, T, I> = fn((&'a T, &'a I)) -> &'a T;
impl<'a> Provider<'a> for Simple {
    type DocumentIter = Copied<btree_set::Iter<'a, Id>>;
    type WordIter = btree_map::Keys<'a, Arc<AlphanumRef>, SimpleDocMap>;
    type WordFilteredIter = Map<
        btree_map::Range<'a, Arc<AlphanumRef>, SimpleDocMap>,
        FirstTy<'a, Arc<AlphanumRef>, SimpleDocMap>,
    >;

    /// O(log n log n)
    fn insert_word(&mut self, word: impl AsRef<str>, document: Id, _index: usize) {
        let word = word.as_ref();
        // SAFETY: We only use `StrPtr` in the current scope.
        let ptr = unsafe { StrPtr::sref(word) };
        if let Some(word_docs) = self.words.get_mut(&Alphanumeral::new(ptr)) {
            word_docs.insert(document);
        } else {
            let mut word_docs = SimpleDocMap::new();
            word_docs.insert(document);
            let word = Alphanumeral::new(word).chars().collect::<String>();
            let ptr = StrPtr::owned(word);
            self.words
                .insert(Arc::new(Alphanumeral::new(ptr)), word_docs);
        }
    }
    /// O(n log n)
    fn remove_document(&mut self, document: Id) {
        for word_docs in self.words.values_mut() {
            word_docs.remove(document);
        }
    }
    /// O(log n log n)
    fn contains_word(&self, word: impl AsRef<str>, document: Id) -> bool {
        let word = word.as_ref();
        // SAFETY: We only use `StrPtr` in the current scope.
        let ptr = unsafe { StrPtr::sref(word) };
        self.words
            .get(&Alphanumeral::new(ptr))
            .map_or(false, |word| word.contains(document))
    }
    /// O(log n)
    ///
    /// Iterator is O(1) - running this and consuming the iterator is O(n log n).
    ///
    /// You can get the length of the list using the [`ExactSizeIterator`] trait.
    fn documents_with_word(&'a self, word: impl AsRef<str>) -> Option<Self::DocumentIter> {
        // SAFETY: We only use `StrPtr` in the current scope.
        let ptr = unsafe { StrPtr::sref(word.as_ref()) };
        self.words
            .get(&Alphanumeral::new(ptr))
            .map(SimpleDocMap::documents)
    }
    fn size(&self) -> usize {
        self.words
            .iter()
            // +16 for Arc size and btree size
            .map(|(word, docs)| word.0.as_ref().len() + 16 + docs.docs.len() * 8 + 16)
            .sum()
    }

    fn word_count_upper_limit(&self) -> usize {
        self.words.len()
    }
    fn word_count_limit(&self) -> usize {
        self.word_count_limit
    }
    fn words(&'a self) -> Self::WordIter {
        self.words.keys()
    }
    fn words_starting_with(&'a self, c: char) -> Self::WordFilteredIter {
        let s1 = String::from(c);
        let ptr1 = StrPtr::owned(s1);
        let s2 = String::from(next_char(c));
        let ptr2 = StrPtr::owned(s2);

        self.words
            .range(Alphanumeral::new(ptr1)..Alphanumeral::new(ptr2))
            .map::<&Arc<AlphanumRef>, _>(|(k, _v)| k)
    }

    fn word_proximity_threshold(&self) -> f32 {
        self.proximity_threshold
    }
    fn word_proximity_algorithm(&self) -> proximity::Algorithm {
        self.proximity_algo
    }
}

#[derive(Debug)]
pub struct SimpleOccurrencesIter<'a, I> {
    iter: I,
    words: ProximateListOrSingle<'a>,

    document_contents: &'a HashMap<Id, Arc<String>>,

    #[allow(clippy::type_complexity)] // That's not complex.
    current: Option<(SplitNonAlphanumeric<'a>, Id, &'a AlphanumRef)>,
    current_doc_matched: bool,

    missing: &'a Mutex<Vec<(Id, &'a AlphanumRef)>>,
}
impl<'a, I: Iterator<Item = (Id, &'a AlphanumRef, f32)>> SimpleOccurrencesIter<'a, I> {
    fn new(
        iter: I,
        words: ProximateListOrSingle<'a>,
        document_contents: &'a HashMap<Id, Arc<String>>,
        missing: &'a Mutex<Vec<(Id, &'a AlphanumRef)>>,
    ) -> Self {
        Self {
            iter,
            words,
            document_contents,
            current: None,
            current_doc_matched: false,
            missing,
        }
    }
}
impl<'a, I: Iterator<Item = (Id, &'a AlphanumRef, f32)>> Iterator for SimpleOccurrencesIter<'a, I> {
    type Item = Occurence;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((words_in_doc, doc_id, searching_word)) = &mut self.current {
            for item in words_in_doc {
                let word_in_doc = item.word();
                let start = item.index();

                // SAFETY: We only use it in this scope.
                let word_ptr = unsafe { StrPtr::sref(word_in_doc) };
                let word_ptr = Alphanumeral::new(word_ptr);

                let word = Alphanumeral::new(word_in_doc);
                if word.chars().next().is_none() {
                    continue;
                }
                if let Some(word_proximity) = self.words.get(&word_ptr) {
                    self.current_doc_matched = true;
                    let rating = (word_proximity - 1.0) * 4.0;
                    let mut occ = Occurence::new(start, *doc_id, 0);
                    *occ.rating_mut() += rating;
                    return Some(occ);
                }
            }

            if !self.current_doc_matched {
                let mut missing = self.missing.lock().expect(
                    "lock is poisoned, other thread panicked.\
                    This should anyway not be accessed from multiple threads simultaneously",
                );
                missing.push((*doc_id, searching_word));
            }
        }

        let (next_doc, word, _) = self.iter.next()?;
        let contents = if let Some(c) = self.document_contents.get(&next_doc) {
            c
        } else {
            return self.next();
        };
        self.current = Some((SplitNonAlphanumeric::new(contents), next_doc, word));
        self.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
#[derive(Debug)]
#[must_use]
pub struct SimpleOccurences<'a> {
    index: &'a Simple,
    word_proximates: &'a proximity::ProximateMap<'a>,
    document_contents: HashMap<Id, Arc<String>>,

    missing: Mutex<Vec<(Id, &'a AlphanumRef)>>,
}
/// Once this is used, call [`Self::missing`] and [`MissingOccurrences::apply`] to remove the missing entries found during
/// the search.
///
/// # Panics
///
/// Using the [`OccurenceProvider::occurrences_of_word`] may panic, if not all documents returned
/// from [`Provider::documents_with_word`]. If a document doesn't exist, still [`Self::add_document`],
/// but with an empty [`String`].
impl<'a> SimpleOccurences<'a> {
    /// The [`proximity::ProximateMap`] can be acquired from
    /// [`crate::query::Documents::take_proximate_map`] which is returned from [`Query::documents`].
    pub fn new(index: &'a Simple, word_proximates: &'a proximity::ProximateMap<'a>) -> Self {
        Self {
            index,
            word_proximates,
            document_contents: HashMap::new(),
            missing: Mutex::new(Vec::new()),
        }
    }
    pub fn add_document(&mut self, id: Id, content: Arc<String>) {
        self.document_contents.insert(id, content);
    }

    /// Remove the missing references.
    #[allow(clippy::missing_panics_doc)]
    pub fn missing(&self) -> MissingOccurrences {
        MissingOccurrences {
            list: self
                .missing
                .lock()
                .unwrap()
                .iter()
                .map(|(id, s)| (*id, s.owned()))
                .collect(),
        }
    }
}
impl<'a> OccurenceProvider<'a> for SimpleOccurences<'a> {
    type Iter =
        SimpleOccurrencesIter<'a, Box<dyn Iterator<Item = (Id, &'a AlphanumRef, f32)> + 'a>>;

    fn occurrences_of_word(&'a self, word: &'a str) -> Option<Self::Iter> {
        if let proximity::Algorithm::Exact = self.index.word_proximity_algorithm() {
            // SAFETY: We only use it in this scope.
            let ptr = unsafe { StrPtr::sref(word) };
            let word_ptr = self.index.words.get_key_value(&Alphanumeral::new(ptr))?.0;

            Some(SimpleOccurrencesIter::new(
                Box::new(
                    self.index
                        .documents_with_word(&**word_ptr)?
                        .map(move |id| (id, &**word_ptr, 1.0)),
                ),
                ProximateListOrSingle::Single(word),
                &self.document_contents,
                &self.missing,
            ))
        } else {
            let words = self.word_proximates.get_panic(word);

            Some(SimpleOccurrencesIter::new(
                Box::new(
                    crate::proximity::proximate_word_docs(self.index, words)
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .map(crate::proximity::ProximateDocItem::into_parts),
                ),
                ProximateListOrSingle::List(words),
                &self.document_contents,
                &self.missing,
            ))
        }
    }
}
/// A list of missing occurrences collected when searching for occurrences using [`SimpleOccurences`].
///
/// This is a result of the data being changed and the index ([`Simple`]) not updating, causing it
/// to think there should be a match when there actually isn't.
///
/// Please call [`Self::apply`] on this.
#[derive(Debug)]
pub struct MissingOccurrences {
    list: Vec<(Id, AlphanumRef)>,
}
impl MissingOccurrences {
    pub fn apply(self, index: &mut Simple) {
        for (id, word) in self.list {
            if let Some(doc_ref) = index.words.get_mut(&word) {
                doc_ref.remove(id);
            }
        }
    }
    #[must_use]
    pub fn list(&self) -> &[(Id, AlphanumRef)] {
        &self.list
    }
}

/// The occurrences of a word in this document.
#[derive(Debug, PartialEq, Eq, Clone)]
#[must_use]
pub struct LosslessDocOccurrences {
    /// A list of the byte index where the start of the word is at.
    occurrences: Vec<usize>,
}
impl LosslessDocOccurrences {
    pub fn new() -> Self {
        Self {
            occurrences: Vec::new(),
        }
    }
}
impl Default for LosslessDocOccurrences {
    fn default() -> Self {
        Self::new()
    }
}
/// The docs this word exists in.
/// Each doc has an associated [`LosslessDocOccurrences`] which keeps track of all the occurrences
/// in that document.
#[derive(Debug, PartialEq, Eq, Clone)]
#[must_use]
pub struct LosslessDocMap {
    /// We need the order of documents to be sorted, as the sorted iterators relies on that.
    docs: BTreeMap<Id, LosslessDocOccurrences>,
}
impl LosslessDocMap {
    pub fn new() -> Self {
        Self {
            docs: BTreeMap::new(),
        }
    }

    /// If `document` has at least one occurrence.
    #[must_use]
    pub fn contains(&self, document: Id) -> bool {
        self.docs.contains_key(&document)
    }
    /// Returns an iterator over the documents with at least one occurrence of the word in
    /// question.
    pub fn documents(&self) -> Copied<btree_map::Keys<'_, Id, LosslessDocOccurrences>> {
        self.docs.keys().copied()
    }

    fn doc(&mut self, document: Id) -> &mut LosslessDocOccurrences {
        self.docs
            .entry(document)
            .or_insert_with(LosslessDocOccurrences::default)
    }
}
impl Default for LosslessDocMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Index which keeps track of all occurrences of all words.
///
/// Much (10x) faster than [`Simple`], but memory usage grows linearly with content added.
/// [`Simple`]s memory usage grows only with word count & document count.
/// If you have relatively short documents, this doesn't take up a lot more memory (only about 2-4x).
#[derive(Debug, Clone)]
#[must_use]
pub struct Lossless {
    words: BTreeMap<Arc<AlphanumRef>, LosslessDocMap>,

    proximity_threshold: f32,
    proximity_algo: proximity::Algorithm,
    word_count_limit: usize,
}
impl Lossless {
    /// `proximity_threshold` is the threshold where alike words are also accepted.
    /// It uses the range [0..1], where values nearer 0 allow more words.
    /// The default is `0.9`.
    ///
    /// `proximity_threshold` is the algorithm used for proximity checking of words.
    ///
    /// `word_count_limit` is the number of words in this index where only words with the first
    /// character is used for approximate matching.
    /// Default is `2_500`.
    pub fn new(
        proximity_threshold: f32,
        proximity_algorithm: proximity::Algorithm,
        word_count_limit: usize,
    ) -> Self {
        Self {
            words: BTreeMap::new(),
            proximity_threshold,
            proximity_algo: proximity_algorithm,
            word_count_limit,
        }
    }
    /// Merges `other` with `self`.
    pub fn ingest(&mut self, other: Self) {
        for (word, docs) in other.words {
            if let Some(my_docs) = self.words.get_mut(&word) {
                for (doc, mut occurrences) in docs.docs {
                    let my = my_docs.doc(doc);

                    my.occurrences.append(&mut occurrences.occurrences);
                    my.occurrences.sort_unstable();
                    my.occurrences.dedup();
                }
            } else {
                self.words.insert(word, docs);
            }
        }
    }
}
/// [`Self::new`] with `proximity_threshold` set to `0.85`.
impl Default for Lossless {
    fn default() -> Self {
        Self::new(0.85, proximity::Algorithm::Hamming, 1000)
    }
}
impl<'a> Provider<'a> for Lossless {
    type DocumentIter = Copied<btree_map::Keys<'a, Id, LosslessDocOccurrences>>;
    type WordIter = btree_map::Keys<'a, Arc<AlphanumRef>, LosslessDocMap>;
    type WordFilteredIter = Map<
        btree_map::Range<'a, Arc<AlphanumRef>, LosslessDocMap>,
        FirstTy<'a, Arc<AlphanumRef>, LosslessDocMap>,
    >;

    /// O(log n log n)
    fn insert_word(&mut self, word: impl AsRef<str>, document: Id, index: usize) {
        let word = word.as_ref();
        // SAFETY: We only use `StrPtr` in the current scope.
        let ptr = unsafe { StrPtr::sref(word) };
        if let Some(word_docs) = self.words.get_mut(&Alphanumeral::new(ptr)) {
            let doc = word_docs.doc(document);
            match doc.occurrences.binary_search(&index) {
                Ok(_) => {}
                Err(idx) => doc.occurrences.insert(idx, index),
            }
        } else {
            let mut word_docs = LosslessDocMap::new();
            word_docs.doc(document).occurrences.push(index);
            let word = Alphanumeral::new(word).chars().collect::<String>();
            let ptr = StrPtr::owned(word);
            self.words
                .insert(Arc::new(Alphanumeral::new(ptr)), word_docs);
        }
    }
    /// O(n log n)
    fn remove_document(&mut self, document: Id) {
        for word_docs in self.words.values_mut() {
            word_docs.docs.remove(&document);
        }
    }
    /// O(log n log n)
    fn contains_word(&self, word: impl AsRef<str>, document: Id) -> bool {
        let word = word.as_ref();
        // SAFETY: We only use `StrPtr` in the current scope.
        let ptr = unsafe { StrPtr::sref(word) };
        self.words
            .get(&Alphanumeral::new(ptr))
            .map_or(false, |word| word.contains(document))
    }
    /// O(log n)
    ///
    /// Iterator is O(1) - running this and consuming the iterator is O(n log n).
    ///
    /// You can get the length of the list using the [`ExactSizeIterator`] trait.
    fn documents_with_word(&'a self, word: impl AsRef<str>) -> Option<Self::DocumentIter> {
        // SAFETY: We only use `StrPtr` in the current scope.
        let ptr = unsafe { StrPtr::sref(word.as_ref()) };
        self.words
            .get(&Alphanumeral::new(ptr))
            .map(LosslessDocMap::documents)
    }
    fn size(&self) -> usize {
        self.words
            .iter()
            .map(|(word, docs)| {
                // +16 for Arc size and btree map
                (word.0.as_ref().len() + 16)
                    + (docs
                        .docs
                        .iter()
                        // 8 for ID, 16 for vec size
                        .map(|(_id, occs)| 8 + occs.occurrences.len() * 8 + 16)
                        .sum::<usize>()
                        + 16)
            })
            .sum()
    }

    fn word_count_upper_limit(&self) -> usize {
        self.words.len()
    }
    fn word_count_limit(&self) -> usize {
        self.word_count_limit
    }
    fn words(&'a self) -> Self::WordIter {
        self.words.keys()
    }
    fn words_starting_with(&'a self, c: char) -> Self::WordFilteredIter {
        let s1 = String::from(c);
        let ptr1 = StrPtr::owned(s1);
        let s2 = String::from(next_char(c));
        let ptr2 = StrPtr::owned(s2);

        self.words
            .range(Alphanumeral::new(ptr1)..Alphanumeral::new(ptr2))
            .map::<&Arc<AlphanumRef>, _>(|(k, _v)| k)
    }

    fn word_proximity_threshold(&self) -> f32 {
        self.proximity_threshold
    }
    fn word_proximity_algorithm(&self) -> proximity::Algorithm {
        self.proximity_algo
    }
}
/// Get occurrences of a word (or similar words) from this [`Lossless`] index.
#[derive(Debug)]
#[must_use]
pub struct LosslessOccurrences<'a> {
    index: &'a Lossless,
    word_proximates: &'a proximity::ProximateMap<'a>,
}
impl<'a> LosslessOccurrences<'a> {
    /// The [`proximity::ProximateMap`] can be acquired from
    /// [`crate::query::Documents::take_proximate_map`] which is returned from [`Query::documents`].
    pub fn new(index: &'a Lossless, word_proximates: &'a proximity::ProximateMap<'a>) -> Self {
        Self {
            index,
            word_proximates,
        }
    }
}
#[derive(Debug)]
pub struct LosslessOccurrencesIter<'a, I> {
    iter: I,

    #[allow(clippy::type_complexity)] // That's not complex.
    current: Option<(core::slice::Iter<'a, usize>, Id, f32)>,
}
impl<'a, I: Iterator<Item = (&'a Vec<usize>, Id, f32)>> LosslessOccurrencesIter<'a, I> {
    fn new(iter: I) -> Self {
        Self {
            iter,
            current: None,
        }
    }
}
impl<'a, I: Iterator<Item = (&'a Vec<usize>, Id, f32)>> Iterator
    for LosslessOccurrencesIter<'a, I>
{
    type Item = Occurence;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((words_in_doc, doc_id, word_proximity)) = &mut self.current {
            if let Some(start) = words_in_doc.next() {
                let rating = (*word_proximity - 1.0) * 4.0;
                let mut occ = Occurence::new(*start, *doc_id, 0);
                *occ.rating_mut() += rating;
                return Some(occ);
            }
        }

        let (occurrences, next_doc, word_proximity) = self.iter.next()?;
        self.current = Some((occurrences.iter(), next_doc, word_proximity));
        self.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
impl<'a> OccurenceProvider<'a> for LosslessOccurrences<'a> {
    type Iter =
        LosslessOccurrencesIter<'a, Box<dyn Iterator<Item = (&'a Vec<usize>, Id, f32)> + 'a>>;
    fn occurrences_of_word(&'a self, word: &'a str) -> Option<Self::Iter> {
        if let proximity::Algorithm::Exact = self.index.word_proximity_algorithm() {
            // SAFETY: We only use it in this scope.
            let ptr = unsafe { StrPtr::sref(word) };
            let word_ptr = self.index.words.get_key_value(&Alphanumeral::new(ptr))?.0;

            Some(LosslessOccurrencesIter::new(Box::new(
                self.index
                    .words
                    .get(&**word_ptr)?
                    .docs
                    .iter()
                    .map(|(id, occs)| (&occs.occurrences, *id, 1.0)),
            )))
        } else {
            let words = self.word_proximates.get_panic(word);

            Some(LosslessOccurrencesIter::new(Box::new(
                crate::proximity::proximate_word_docs(self.index, words)
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .map(crate::proximity::ProximateDocItem::into_parts)
                    .map(|(id, word, rating)| {
                        (&self.index.words[word].docs[&id].occurrences, id, rating)
                    }),
            )))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Alphanumeral, DocumentMap, Id, Lossless, LosslessOccurrences, Occurence, OccurenceProvider,
        Provider, Simple, SimpleOccurences,
    };

    fn doc1() -> &'static str {
        "\
Lorem ipsum dolor sit amet, consectetur adipiscing elit. Mauris interdum, metus ut consectetur ullamcorper, velit mi placerat diam, vitae rutrum quam magna sit amet lacus. Curabitur ut rutrum ante. Pellentesque vel neque ante. Nullam vel velit ut ipsum luctus varius id porta nisi. Morbi hendrerit, nunc non consequat consequat, dolor mi consectetur eros, vitae varius diam leo in sem. Aliquam erat volutpat. Proin id mollis quam. Morbi venenatis tincidunt nunc eget ullamcorper. Cras hendrerit libero enim, et aliquet diam rutrum ut. Duis auctor ligula libero, cursus ullamcorper libero porttitor eget. Aliquam scelerisque ac elit at condimentum. Fusce sit amet purus posuere, suscipit libero id, tincidunt nulla. Aliquam molestie orci vitae tellus commodo, nec mattis purus efficitur. Quisque quam nisl, fermentum sit amet ante vitae, finibus aliquet nunc. Ut ut hendrerit lorem.

Nam porttitor urna leo, sit amet imperdiet libero vulputate sed. Morbi elementum ligula turpis, at mattis risus finibus vitae. Vestibulum id egestas tortor. Curabitur suscipit nulla dolor. Duis rhoncus et felis dignissim bibendum. Sed congue arcu quis lacinia iaculis. Nam sit amet lacus sit amet lacus efficitur bibendum."
    }
    fn doc2() -> &'static str {
        "\
Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla lectus orci, aliquam ut justo varius, consequat semper enim. Vestibulum porttitor justo sed tincidunt fringilla. Donec sit amet sollicitudin mi, eu bibendum orci. Maecenas at feugiat ipsum. Vestibulum libero dolor, egestas et sollicitudin eu, ornare sit amet mauris. Maecenas in dolor volutpat, rhoncus urna id, luctus sem. Nulla pulvinar non ex eu venenatis.

Aliquam euismod, justo eu viverra ornare, ex nisi interdum neque, in rutrum nunc mi sit amet libero. Aenean nec arcu pulvinar, venenatis erat ac, sodales massa. Morbi quam leo, cursus at est a, placerat aliquam mauris. Pellentesque habitant morbi tristique senectus et netus et malesuada fames ac turpis egestas. In hac habitasse platea dictumst. In consectetur aliquet aliquam. In vel tempor elit, eget auctor dolor. Phasellus molestie est eget posuere imperdiet. Donec sagittis tincidunt facilisis. Sed eu pulvinar lectus, euismod dictum tellus. Nulla lacinia diam quis odio ultrices, viverra dictum arcu mollis. Donec tempor diam eget tristique maximus. Etiam a dui eu augue euismod dignissim."
    }

    #[test]
    fn alphanumerical() {
        let s1 = Alphanumeral::new("test-is good!");
        let s2 = Alphanumeral::new("TESTIsGood");
        assert_eq!(s1, s2);
        assert_eq!(s1.cmp(&s2), std::cmp::Ordering::Equal);
        assert_eq!(s1.cmp(&"TestIsGood1".into()), std::cmp::Ordering::Less);
        assert_eq!(s1.cmp(&"TestIsGooc".into()), std::cmp::Ordering::Greater);
        assert_eq!(s1.cmp(&"TestIsGooe".into()), std::cmp::Ordering::Less);
    }

    #[test]
    fn occurences_simple() {
        let mut doc_map = DocumentMap::new();
        let mut index = Simple::new(1.0, crate::proximity::Algorithm::Exact, 100);
        doc_map.insert("doc1", doc1(), &mut index);
        doc_map.insert("doc3", doc2(), &mut index);

        assert!(index.contains_word("lorem", doc_map.get_id("doc1").unwrap()));
        assert!(index.contains_word("lorem", doc_map.get_id("doc3").unwrap()));
        assert_eq!(doc_map.get_id("doc3"), Some(Id::new(1)));
        assert_eq!(doc_map.get_id("doc2"), None);

        let proximate_map = crate::proximity::ProximateMap::new();

        let mut simple_provider = SimpleOccurences::new(&index, &proximate_map);
        simple_provider.add_document(doc_map.get_id("doc1").unwrap(), doc1().to_string().into());
        simple_provider.add_document(doc_map.get_id("doc3").unwrap(), doc2().to_string().into());

        let mut occurrences = simple_provider.occurrences_of_word("lorem").unwrap();
        // Same problem here as above
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(0, doc_map.get_id("doc1").unwrap(), 0))
        );
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(875, doc_map.get_id("doc1").unwrap(), 0))
        );
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(0, doc_map.get_id("doc3").unwrap(), 0))
        );
        assert_eq!(occurrences.next(), None);
    }
    #[test]
    fn occurences_lossless() {
        let mut doc_map = DocumentMap::new();
        let mut index = Lossless::new(1.0, crate::proximity::Algorithm::Exact, 100);
        doc_map.insert("doc1", doc1(), &mut index);
        doc_map.insert("doc3", doc2(), &mut index);

        assert!(index.contains_word("lorem", doc_map.get_id("doc1").unwrap()));
        assert!(index.contains_word("lorem", doc_map.get_id("doc3").unwrap()));
        assert_eq!(doc_map.get_id("doc3"), Some(Id::new(1)));
        assert_eq!(doc_map.get_id("doc2"), None);

        let proximate_map = crate::proximity::ProximateMap::new();

        let lossless_provider = LosslessOccurrences::new(&index, &proximate_map);

        let mut occurrences = lossless_provider.occurrences_of_word("lorem").unwrap();
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(0, doc_map.get_id("doc1").unwrap(), 0))
        );
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(875, doc_map.get_id("doc1").unwrap(), 0))
        );
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(0, doc_map.get_id("doc3").unwrap(), 0))
        );
        assert_eq!(occurrences.next(), None);
    }
}
