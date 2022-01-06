use std::fmt::Debug;

use crate::index::{AlphanumRef, Id, Provider};

#[derive(Debug)]
enum PIter<'a, WI: Iterator<Item = &'a AlphanumRef>, WFI: Iterator<Item = &'a AlphanumRef>> {
    WordIter(WI),
    WordFilteredIter(WFI),
}
impl<'a, WI: Iterator<Item = &'a AlphanumRef>, WFI: Iterator<Item = &'a AlphanumRef>> Iterator
    for PIter<'a, WI, WFI>
{
    type Item = &'a AlphanumRef;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::WordIter(i) => i.next(),
            Self::WordFilteredIter(i) => i.next(),
        }
    }
}

#[derive(Debug)]
pub struct ProximateWordIter<'a, P: Provider<'a>> {
    word: &'a str,
    iter: PIter<'a, P::WordIter, P::WordFilteredIter>,
    threshold: f64,
}
impl<'a, P: Provider<'a>> Iterator for ProximateWordIter<'a, P> {
    type Item = (&'a AlphanumRef, f32);
    fn next(&mut self) -> Option<Self::Item> {
        for other_word in &mut self.iter {
            let similarity = algo::jaro(other_word.chars(), self.word.chars());

            if similarity > self.threshold {
                #[allow(clippy::cast_possible_truncation)]
                return Some((other_word, similarity as f32));
            }
        }
        None
    }
}
/// If `threshold` is closer to 0, more results are accepted.
/// It has a range of [0..1].
/// E.g. `0.95` means `word` is probably the only word to match.
pub fn proximate_words<'a, P: Provider<'a>>(
    word: &'a str,
    provider: &'a P,
) -> ProximateWordIter<'a, P> {
    let threshold = provider.word_proximity_threshold();
    if let Some(c) = word.chars().next() {
        if provider.word_count_upper_limit() > provider.word_count_limit() {
            return ProximateWordIter {
                word,
                iter: PIter::WordFilteredIter(provider.words_starting_with(c)),
                threshold,
            };
        }
    }
    ProximateWordIter {
        word,
        iter: PIter::WordIter(provider.words()),
        threshold,
    }
}

pub struct ProximateDocIter<'a, P: Provider<'a>> {
    word_iter: ProximateWordIter<'a, P>,
    provider: &'a P,
    current: Option<(&'a AlphanumRef, P::DocumentIter, f32)>,
    // Why BTreeSet? Well, faster on small lists, as hashing takes a long time
    // compared to 10 comparisons (2¹⁰ = 1024 accepted words).
    // `TODO`: Use this.
    // That would mean taking this after the `Query::documents` iterator was complete. How would we
    // do this? Downcasting? Wouldn't that just be as hurting to performance?
    // Refactoring?
    // accepted_words: BTreeSet<&'a AlphanumRef>,
}
impl<'a, P: Provider<'a> + Debug> Debug for ProximateDocIter<'a, P>
where
    P::DocumentIter: Debug,
    P::WordIter: Debug,
    P::WordFilteredIter: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProximateDocIter")
            .field("word_iter", &self.word_iter)
            .field("provider", &self.provider)
            .field("current", &self.current)
            .finish()
    }
}
// impl<'a, P: Provider<'a>> ProximateDocIter<'a, P> {
// pub(crate) fn accepted_words(&self) -> &BTreeSet<&'a AlphanumRef> {
// &self.accepted_words
// }
// pub(crate) fn take_accepted_words(&mut self) -> BTreeSet<&AlphanumRef> {
// std::mem::take(&mut self.accepted_words)
// }
// }
impl<'a, P: Provider<'a>> Iterator for ProximateDocIter<'a, P> {
    type Item = (Id, &'a AlphanumRef, f32);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((word, doc_iter, proximity)) = &mut self.current {
            if let Some(doc) = doc_iter.next() {
                Some((doc, word, *proximity))
            } else {
                self.current = None;
                self.next()
            }
        } else if let Some((next_word, proximity)) = self.word_iter.next() {
            self.current = self
                .provider
                .documents_with_word(next_word)
                .map(|iter| (next_word, iter, proximity));
            // self.accepted_words.insert(next_word);
            self.next()
        } else {
            None
        }
    }
}
/// `word_count_limit` is the limit where only words starting with the first [`char`] of `word`
/// will be checked for proximity.
pub fn proximate_word_docs<'a, P: Provider<'a>>(
    word: &'a str,
    provider: &'a P,
) -> ProximateDocIter<'a, P> {
    ProximateDocIter {
        word_iter: proximate_words(word, provider),
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
            1.0 / (0.05 * differences as f64 + 1.0)
        }
    }
}
