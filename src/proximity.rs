//! Word similarity for typo tolerance and matching beginning of words.

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

/// The string proximity algorithm to use.
///
/// See [`strsim`] for more details on these algorithms,
/// as that's the library which provide them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Algorithm {
    /// about 10x as slow as [`Self::Exact`],
    /// but actually accepts similar words.
    Hamming,
    /// 2x-ish as slow as [`Self::Hamming`],
    /// but produces higher quality.
    /// Performance hit still nothing compared to parsing a small HTML document.
    Jaro,
    /// Only exact matches are accepted. The absolute fastest.
    Exact,
}
impl Algorithm {
    /// Get the similarity between two iterators of [`char`]s.
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
impl Default for Algorithm {
    fn default() -> Self {
        Self::Jaro
    }
}

/// A list of words close to the target word, and their "rating".
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
    pub(crate) fn get_or_panic(&'a self, word: &str) -> &'a ProximateList {
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

/// An item of the [`ProximateWordIter`], returned from [`proximate_words`].
#[derive(Debug, PartialEq, PartialOrd)]
#[must_use]
pub struct ProximateWordItem<'a> {
    /// The found word.
    pub word: &'a Arc<AlphanumRef>,
    /// The word's likeness. Higher is better.
    pub rating: f32,
}
impl<'a> ProximateWordItem<'a> {
    /// Wrap a new [`ProximateWordItem`]. Works well with [`Self::into_parts`].
    pub fn new(item: (&'a Arc<AlphanumRef>, f32)) -> Self {
        Self {
            word: item.0,
            rating: item.1,
        }
    }
    /// Turn `self` into parts. Works well with [`Self::new`].
    #[must_use]
    pub fn into_parts(self) -> (&'a Arc<AlphanumRef>, f32) {
        (self.word, self.rating)
    }
}
/// An iterator over the words with high likeness to the target word, as provided when running
/// [`proximate_words`].
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
                    return Some(ProximateWordItem::new((other_word, similarity)));
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
                        .take(self.word.chars().count())
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

/// An item found by [`ProximateDocIter`], an occurrence of [`ProximateWordItem`] in any of the
/// documents in the [`Provider`] passed to [`proximate_word_docs`].
#[derive(Debug)]
#[must_use]
pub struct ProximateDocItem<'a> {
    /// Document id
    pub id: Id,
    /// word we found
    pub word: &'a AlphanumRef,
    /// It's proximity compared to the original. Higher is more similar.
    pub rating: f32,
}
impl<'a> PartialEq for ProximateDocItem<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.word == other.word
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
        let cmp = self.id.cmp(&other.id);
        if cmp.is_eq() {
            self.word.cmp(other.word)
        } else {
            cmp
        }
    }
}
impl<'a> ProximateDocItem<'a> {
    /// Wrap a new [`ProximateDocItem`]. Works well with [`Self::into_parts`].
    pub fn new(item: (Id, &'a AlphanumRef, f32)) -> Self {
        Self {
            id: item.0,
            word: item.1,
            rating: item.2,
        }
    }
    /// Turn `self` into parts. Works well with [`Self::new`].
    #[must_use]
    pub fn into_parts(self) -> (Id, &'a AlphanumRef, f32) {
        (self.id, self.word, self.rating)
    }
}

/// See [`proximate_word_docs`].
#[derive(Debug)]
pub struct ProximateDocIter<'a, P: Provider<'a>> {
    word_iter: btree_map::Iter<'a, Arc<AlphanumRef>, f32>,
    provider: &'a P,
    current: Option<(&'a Arc<AlphanumRef>, P::DocumentIter, f32)>,
}
impl<'a, P: Provider<'a>> Iterator for ProximateDocIter<'a, P> {
    type Item = ProximateDocItem<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((word, doc_iter, proximity)) = &mut self.current {
                if let Some(doc) = doc_iter.next() {
                    return Some(ProximateDocItem::new((doc, word, *proximity)));
                }
                self.current = None;
                continue;
            }
            if let Some((next_word, proximity)) = self.word_iter.next() {
                self.current = self
                    .provider
                    .documents_with_word(&**next_word)
                    .map(|iter| (next_word, iter, *proximity));
                continue;
            }
            return None;
        }
    }
}

/// Search for `words` in `provider`.
///
/// The output isn't ordered according to document IDs.
///
/// Use [`ProximateDocItem`] and [`Iterator::collect`] to map the iterator to the
/// `ProximateDocItem`, then collect it in a [`BTreeSet`](std::collections::BTreeSet), then [`IntoIterator::into_iter`] and map
/// again.
pub fn proximate_word_docs<'a, P: Provider<'a>>(
    provider: &'a P,
    words: &'a ProximateList,
) -> ProximateDocIter<'a, P> {
    ProximateDocIter {
        word_iter: words.words.iter(),
        current: None,
        provider,
    }
}

/// String similarity algorithms.
#[allow(clippy::missing_panics_doc)] // They don't happen.
pub mod algo {
    struct IntoIterClone<I: Iterator<Item = char> + Clone>(I);
    impl<'a, I: Iterator<Item = char> + Clone> IntoIterator for &'a IntoIterClone<I> {
        type IntoIter = I;
        type Item = char;
        fn into_iter(self) -> Self::IntoIter {
            self.0.clone()
        }
    }

    /// Helper trait for [`char`] [`Iterator`]s which are also [`Clone`].
    pub trait IClo: Iterator<Item = char> + Clone {}
    impl<T: Iterator<Item = char> + Clone> IClo for T {}

    /// The currently used default.
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
