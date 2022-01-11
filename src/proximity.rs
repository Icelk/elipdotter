use std::collections::{btree_map, BTreeMap};
use std::fmt::Debug;
use std::sync::Arc;

use crate::index::{AlphanumRef, Alphanumeral, Id, Provider};

#[derive(Debug)]
enum PIter<
    'a,
    WI: Iterator<Item = &'a Arc<AlphanumRef>>,
    WFI: Iterator<Item = &'a Arc<AlphanumRef>>,
> {
    WordIter(WI),
    WordFilteredIter(WFI),
}
impl<'a, WI: Iterator<Item = &'a Arc<AlphanumRef>>, WFI: Iterator<Item = &'a Arc<AlphanumRef>>>
    Iterator for PIter<'a, WI, WFI>
{
    type Item = &'a Arc<AlphanumRef>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::WordIter(i) => i.next(),
            Self::WordFilteredIter(i) => i.next(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Algorithm {
    /// about 10x as slow as [`Self::Exact`],
    /// but actually accepts similar words.
    Hamming,
    /// 2x as slow as [`Self::Hamming`],
    /// but produces higher quality.
    /// Still nothing compared to parsing of HTML.
    Jaro,
    /// Only exact matches are accepted. The absolute fastest.
    Exact,
}
impl Algorithm {
    pub fn similarity(&self, a: impl algo::IClo, b: impl algo::IClo) -> f64 {
        match self {
            Self::Hamming => algo::hamming(a, b),
            Self::Jaro => algo::jaro(a, b),
            Self::Exact => {
                if a.into_iter().eq(b.into_iter()) {
                    1.0
                } else {
                    0.0
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
#[must_use]
pub struct ProximateList {
    pub(crate) words: BTreeMap<Arc<AlphanumRef>, f32>,
}
/// Map of words to their [`ProximateList`].
#[derive(Debug, Clone)]
#[must_use]
pub struct ProximateMap<'a> {
    pub(crate) map: BTreeMap<&'a str, ProximateList>,
}
impl<'a> ProximateMap<'a> {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
    pub(crate) fn get_panic(&'a self, word: &str) -> &'a ProximateList {
        fn panic_missing_proximate_words(word: &str) -> ! {
            panic!("Missing proximate words when iterating over occurrences of word {}. Check you are passing the correct `proximity::ProximateMap`.", word)
        }

        if let Some(s) = self.map.get(word) {
            s
        } else {
            panic_missing_proximate_words(word)
        }
    }
}
impl<'a> Default for ProximateMap<'a> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, PartialEq, PartialOrd)]
#[must_use]
pub struct ProximateWordItem<'a> {
    pub word: &'a Arc<AlphanumRef>,
    pub rating: f32,
}
impl<'a> ProximateWordItem<'a> {
    pub fn new(item: (&'a Arc<AlphanumRef>, f32)) -> Self {
        Self {
            word: item.0,
            rating: item.1,
        }
    }
    #[must_use]
    pub fn into_parts(self) -> (&'a Arc<AlphanumRef>, f32) {
        (self.word, self.rating)
    }
}
#[derive(Debug)]
pub struct ProximateWordIter<'a, 'b, P: Provider<'a>> {
    word: &'b str,
    iter: PIter<'a, P::WordIter, P::WordFilteredIter>,
    threshold: f32,
    algo: Algorithm,
}
impl<'a, 'b, P: Provider<'a>> ProximateWordIter<'a, 'b, P> {
    pub fn extend_proximates(self, proximates: &mut ProximateMap<'b>) {
        proximates.map.insert(
            self.word,
            ProximateList {
                words: self
                    .map(|item| (Arc::clone(item.word), item.rating))
                    .collect(),
            },
        );
    }
}
impl<'a, 'b, P: Provider<'a>> Iterator for ProximateWordIter<'a, 'b, P> {
    type Item = ProximateWordItem<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let iter = &mut self.iter;
        if self.word.len() < 3 {
            for other_word in iter {
                #[allow(clippy::cast_possible_truncation)]
                let similarity = self.algo.similarity(other_word.chars(), self.word.chars()) as f32;

                if similarity > self.threshold {
                    #[allow(clippy::cast_possible_truncation)]
                    return Some(ProximateWordItem::new((other_word, similarity as f32)));
                }
            }
        } else {
            for other_word in iter {
                // Starts with
                let other_len = other_word.chars().count();
                let len_diff = other_len.checked_sub(self.word.len());
                if let Some(len_diff) = len_diff {
                    if other_word
                        .chars()
                        .take(self.word.len())
                        .eq(self.word.chars())
                    {
                        if len_diff == 0 {
                            return Some(ProximateWordItem::new((other_word, 1.0)));
                        }
                        #[allow(clippy::cast_precision_loss)]
                        return Some(ProximateWordItem::new((
                            other_word,
                            1.0 / ((0.05 * len_diff as f32) + 0.5) - 1.2,
                        )));
                    }
                }

                // Similarity
                #[allow(clippy::cast_possible_truncation)]
                let similarity = self.algo.similarity(other_word.chars(), self.word.chars()) as f32;

                if similarity >= self.threshold {
                    return Some(ProximateWordItem::new((other_word, similarity)));
                }
            }
        }
        None
    }
}
/// If `threshold` is closer to 0, more results are accepted.
/// It has a range of [0..1].
/// E.g. `0.95` means `word` is probably the only word to match.
pub fn proximate_words<'a, 'b, P: Provider<'a>>(
    word: &'b str,
    provider: &'a P,
) -> ProximateWordIter<'a, 'b, P> {
    let threshold = provider.word_proximity_threshold();
    if let Some(c) = Alphanumeral::new(word).chars().next() {
        if provider.word_count_upper_limit() > provider.word_count_limit() {
            let iter = PIter::WordFilteredIter(provider.words_starting_with(c));
            return ProximateWordIter {
                word,
                iter,
                threshold,
                algo: provider.word_proximity_algorithm(),
            };
        }
    }
    ProximateWordIter {
        word,
        iter: PIter::WordIter(provider.words()),
        threshold,
        algo: provider.word_proximity_algorithm(),
    }
}

#[derive(Debug)]
#[must_use]
pub struct ProximateDocItem<'a> {
    pub id: Id,
    pub word: &'a AlphanumRef,
    pub rating: f32,
}
impl<'a> PartialEq for ProximateDocItem<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl<'a> Eq for ProximateDocItem<'a> {}
impl<'a> PartialOrd for ProximateDocItem<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<'a> Ord for ProximateDocItem<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}
impl<'a> ProximateDocItem<'a> {
    pub fn new(item: (Id, &'a AlphanumRef, f32)) -> Self {
        Self {
            id: item.0,
            word: item.1,
            rating: item.2,
        }
    }
    #[must_use]
    pub fn into_parts(self) -> (Id, &'a AlphanumRef, f32) {
        (self.id, self.word, self.rating)
    }
}

#[derive(Debug)]
pub struct ProximateDocIter<'a, P: Provider<'a>> {
    // word_iter: ProximateWordIter<'a, 'b, P>,
    word_iter: btree_map::Iter<'a, Arc<AlphanumRef>, f32>,
    // words: &'a WordProximates<'a>,
    provider: &'a P,
    current: Option<(&'a Arc<AlphanumRef>, P::DocumentIter, f32)>,
    // Why BTreeSet? Well, faster on small lists, as hashing takes a long time
    // compared to 10 comparisons (2¹⁰ = 1024 accepted words).
    // `TODO`: Use this.
    // That would mean taking this after the `Query::documents` iterator was complete. How would we
    // do this? Downcasting? Wouldn't that just be as hurting to performance?
    // Refactoring?
    // accepted_words: BTreeSet<&'a AlphanumRef>,
}
// impl<'a, P: Provider<'a> + Debug> Debug for ProximateDocIter<'a, P>
// where
// P::DocumentIter: Debug,
// P::WordIter: Debug,
// P::WordFilteredIter: Debug,
// {
// fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
// f.debug_struct("ProximateDocIter")
// .field("words", &self.words)
// .field("provider", &self.provider)
// .field("current", &self.current)
// .finish()
// }
// }
// impl<'a, P: Provider<'a>> ProximateDocIter<'a, P> {
// pub(crate) fn accepted_words(&self) -> &BTreeSet<&'a AlphanumRef> {
// &self.accepted_words
// }
// pub(crate) fn take_accepted_words(&mut self) -> BTreeSet<&AlphanumRef> {
// std::mem::take(&mut self.accepted_words)
// }
// }
impl<'a, P: Provider<'a>> Iterator for ProximateDocIter<'a, P> {
    type Item = ProximateDocItem<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((word, doc_iter, proximity)) = &mut self.current {
            if let Some(doc) = doc_iter.next() {
                Some(ProximateDocItem::new((doc, word, *proximity)))
            } else {
                self.current = None;
                self.next()
            }
        } else if let Some((next_word, proximity)) = self.word_iter.next() {
            self.current = self
                .provider
                .documents_with_word(&**next_word)
                .map(|iter| (next_word, iter, *proximity));
            // self.accepted_words.insert(next_word);
            self.next()
        } else {
            None
        }
    }
}
/// The output isn't ordered according to document IDs.
///
/// Use [`ProximateDocItem`] and [`Iterator::collect`] to map the iterator to the
/// `ProximateDocItem`, then collect it in a [`BTreeSet`], then [`IntoIterator::into_iter`] and map
/// again.
pub fn proximate_word_docs<'a, P: Provider<'a>>(
    provider: &'a P,
    words: &'a ProximateList,
) -> ProximateDocIter<'a, P> {
    ProximateDocIter {
        // word_iter: proximate_words(word, provider),
        word_iter: words.words.iter(),
        // words: word_proximates,
        current: None,
        provider,
        // accepted_words: BTreeSet::new(),
    }
}

// They don't happen.
#[allow(clippy::missing_panics_doc)]
pub mod algo {
    struct IntoIterClone<I: Iterator<Item = char> + Clone>(I);
    impl<'a, I: Iterator<Item = char> + Clone> IntoIterator for &'a IntoIterClone<I> {
        type IntoIter = I;
        type Item = char;
        fn into_iter(self) -> Self::IntoIter {
            self.0.clone()
        }
    }

    pub trait IClo: Iterator<Item = char> + Clone {}
    impl<T: Iterator<Item = char> + Clone> IClo for T {}

    /// The currently used.
    pub fn jaro(a: impl IClo, b: impl IClo) -> f64 {
        strsim::generic_jaro(&IntoIterClone(a), &IntoIterClone(b))
    }
    /// 5-10x faster than [`jaro`], but is quality same?
    pub fn hamming(a: impl IClo, b: impl IClo) -> f64 {
        let a = IntoIterClone(a);
        let b = IntoIterClone(b);

        let a_count = a.into_iter().count();
        let b_count = b.into_iter().count();

        let min = std::cmp::min(a_count, b_count);
        let max = std::cmp::max(a_count, b_count);
        let len_diff = max - min;

        let clamped_a = a.into_iter().take(min);
        let clamped_b = b.into_iter().take(min);

        // UNWRAP: They have the same length - ↑ .take
        let mut differences =
            strsim::generic_hamming(&IntoIterClone(clamped_a), &IntoIterClone(clamped_b)).unwrap();
        differences += len_diff;

        // We don't care about precision.
        #[allow(clippy::cast_precision_loss)]
        {
            1.0 / (1.0 * (differences as f64 / min as f64) + 1.0)
        }
    }
}
