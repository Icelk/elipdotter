//! # Big O notation reference
//!
//! `O(1) < O(log n) < O(log n * log n) < O(sqrt(n)) < O(n) < O(n * log n) < O(n^1.1) < O(n²) < O(n³) < O(2^n)`
//! `O(sqrt(n))` is true for all `sqrt(n^m)` where `0<m<1`.
//!
//! Since `O(log n)` is very close to `O(1)`,
//! `O(log n * log n)` is also and
//! `O(n * log n)` is very close to `O(n)`.

use std::ascii::AsciiExt;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Debug;
use std::sync::Arc;

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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct Occurence(usize);
impl Occurence {
    fn new(pos: usize) -> Self {
        Self(pos)
    }
    #[must_use]
    pub fn start(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Hash)]
pub struct Alphanumeral<T>(T);
impl<T> Alphanumeral<T> {
    pub fn new(s: T) -> Self {
        Self(s)
    }
}
impl<T: AsRef<str>> AsRef<str> for Alphanumeral<T> {
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}
impl<T1: AsRef<str>, T2: AsRef<str>> PartialEq<T1> for Alphanumeral<T2> {
    fn eq(&self, other: &T1) -> bool {
        let mut me = self.0.as_ref().chars();
        let mut other = other.as_ref().chars();
        loop {
            let me_c = loop {
                let n = me.next();
                if n.map_or(false, |n| !n.is_alphanumeric()) {
                    continue;
                }
                break n;
            };
            let other_c = loop {
                let n = other.next();
                if n.map_or(false, |n| !n.is_alphanumeric()) {
                    continue;
                }
                break n;
            };
            if me_c != other_c {
                return false;
            }
            if me_c.is_none() {
                break;
            }
        }
        true
    }
}
impl<T: AsRef<str>> Eq for Alphanumeral<T> {}

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
    /// Alternatively, [`Self::reserve_id`] and then drop the lock, go to a different thread, and
    /// make a new [`Simple`]. [`ProviderCore::digest_document`], then [`ProviderCore::ingest`] the
    /// second index into the first.
    #[allow(clippy::missing_panics_doc)]
    pub fn insert(
        &mut self,
        name: impl Into<String>,
        content: &str,
        provider: &mut impl Provider,
    ) {
        let name = name.into();

        if let Some(id) = self.get_id(&name) {
            provider.digest_document(id, content);
            return;
        }

        let id = self.get_first();

        self.name_to_id.insert(name.clone(), id);
        let old_doc = self.id_to_name.insert(id, name);
        assert_eq!(old_doc, None);
        provider.digest_document(id, content);
    }
    fn get_first(&self) -> Id {
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
    #[must_use]
    pub fn get_name(&self, id: Id) -> Option<&str> {
        self.id_to_name.get(&id).map(|s| &**s)
    }

    // Option:
    //  If we have UUIDs instead, we can just remove the Id from `self`,
    //  as any attempts to resolve that into a path will fail.
    #[allow(clippy::missing_panics_doc)]
    pub fn force_remove(&mut self, document: Id, provider: &mut impl Provider) {
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

#[derive(Debug)]
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
/// Allows to insert words and remove occurrences from documents.
pub trait ProviderCore {
    fn insert_word<'a>(&mut self, word: impl Into<Cow<'a, str>>, document: Id);
    fn remove_document(&mut self, document: Id);
    fn contains_word(&self, word: impl AsRef<str>, document: Id) -> bool;

    /// Only adds words which are alphanumeric.
    fn digest_document(&mut self, id: Id, content: &str) {
        for word in content.split_whitespace() {
            // Word must be alphanumeric to be added.
            if word.contains(|c: char| !c.is_alphanumeric()) {
                continue;
            }

            self.insert_word(word, id);
        }
    }
}

#[derive(Debug)]
#[must_use]
pub struct SimpleDocRef {
    docs: BTreeSet<Id>,
}
impl SimpleDocRef {
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
    pub fn documents(&self) -> impl Iterator<Item = Id> + ExactSizeIterator + '_ {
        self.docs.iter().copied()
    }
}
impl Default for SimpleDocRef {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
#[must_use]
pub struct Simple {
    words: BTreeMap<String, SimpleDocRef>,
}
impl Simple {
    pub fn new() -> Self {
        Self {
            words: BTreeMap::new(),
        }
    }

    /// O(log n)
    ///
    /// Iterator is O(1) - running this and consuming the iterator is O(n log n).
    ///
    /// You can get the length of the list using the [`ExactSizeIterator`] trait.
    pub fn documents_with_word(
        &self,
        word: impl AsRef<str>,
    ) -> Option<impl Iterator<Item = Id> + ExactSizeIterator + '_> {
        self.words.get(word.as_ref()).map(SimpleDocRef::documents)
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
impl Default for Simple {
    fn default() -> Self {
        Self::new()
    }
}
impl<'b> Provider for Simple {
    /// O(log n log n)
    fn insert_word<'a>(&mut self, word: impl Into<Cow<'a, str>>, document: Id) {
        let cow = word.into();
        if let Some(doc_ref) = self.words.get_mut(&*cow) {
            doc_ref.insert(document);
        } else {
            let mut doc_ref = SimpleDocRef::new();
            doc_ref.insert(document);
            self.words.insert(cow.into_owned(), doc_ref);
        }
    }
    /// O(n log n)
    fn remove_document(&mut self, document: Id) {
        for doc_ref in self.words.values_mut() {
            doc_ref.remove(document);
        }
    }
    /// O(log n log n)
    fn contains_word(&self, word: impl AsRef<str>, document: Id) -> bool {
        let word = word.as_ref();
        self.words
            .get(word)
            .map_or(false, |word| word.contains(document))
    }
}
fn word_pattern(c: char) -> bool {
    c.is_ascii_whitespace() || c.is_ascii_punctuation()
}
#[derive(Debug)]
pub struct SimpleOccurrencesIter<'a> {
    iter: std::collections::btree_set::Iter<'a, Id>,
    word: &'a str,

    document_contents: &'a HashMap<Id, Arc<String>>,

    current_doc: Option<(std::str::Split<'a, fn(char) -> bool>, Id)>,
    current_pos: usize,
    current_doc_matched: bool,

    missing: &'a mut Vec<Id>,
}
impl<'a> SimpleOccurrencesIter<'a> {
    fn new(
        doc_ref: &'a SimpleDocRef,
        word: &'a str,
        document_contents: &'a HashMap<Id, Arc<String>>,
        missing: &'a mut Vec<Id>,
    ) -> Self {
        Self {
            iter: doc_ref.docs.iter(),
            word,
            document_contents,
            current_doc: None,
            current_pos: 0,
            current_doc_matched: false,
            missing,
        }
    }

    // fn new(doc_ref: &'a SimpleDocRef) -> Self {
    // Self {
    // original: doc_ref,
    // iter: doc_ref.docs.iter(),
    // }
    // }
    // pub fn clone_from_start(&self) -> Self {
    // Self::new(self.original)
    // }
}
impl<'a> Iterator for SimpleOccurrencesIter<'a> {
    type Item = Occurence;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((doc_iter, doc_id)) = &mut self.current_doc {
            for doc in doc_iter {
                let start = self.current_pos;
                self.current_pos += doc.len() + 1;
                if doc.is_empty() {
                    continue;
                }
                if doc == self.word {
                    self.current_doc_matched = true;
                    return Some(Occurence::new(start));
                }
            }

            if !self.current_doc_matched {
                self.missing.push(*doc_id);
            }
        }

        let next_doc = self.iter.next()?;
        let contents = if let Some(c) = self.document_contents.get(next_doc) {
            c
        } else {
            failed_to_find_document_in_provided_documents()
        };
        self.current_doc = Some((contents.split(word_pattern), *next_doc));
        self.current_pos = 0;
        self.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
fn failed_to_find_document_in_provided_documents() -> ! {
    panic!("Tried to get a document from the provided documents in `SimpleProvider`, but failed.")
}
#[derive(Debug)]
#[must_use]
pub struct SimpleProvider<'a> {
    index: &'a Simple,
    document_contents: HashMap<Id, Arc<String>>,

    missing: Vec<Id>,
}
impl<'a> SimpleProvider<'a> {
    pub fn new(index: &'a Simple) -> Self {
        Self {
            index,
            document_contents: HashMap::new(),
            missing: Vec::new(),
        }
    }
    pub fn add_document(&mut self, id: Id, content: Arc<String>) {
        self.document_contents.insert(id, content);
    }
    pub fn occurrences_of_word(&'a mut self, word: &'a str) -> Option<SimpleOccurrencesIter<'a>> {
        let doc_ref = self.index.words.get(word)?;
        Some(SimpleOccurrencesIter::new(
            doc_ref,
            word,
            &self.document_contents,
            &mut self.missing,
        ))
    }
}
// Simple with read data. If cache doesn't contain the needed word, panic.
// Write about this behaviour in the docs. Make clear you have to add all the ones
// you plan on looking up to the cache.
//
// When query resolves to more than 100 documents, cap?
// How to determine which to use?
// Say the query gave too many documents and do nothing?
//
// When digesting, spawn tasks. Make their own Simple, which can be merged. They'll only check each
// word once, instead of x times, where x is the occurrences of the word in the text.
