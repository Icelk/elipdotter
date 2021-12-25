use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Debug;

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
    pub fn insert(
        &mut self,
        name: impl Into<String>,
        content: &str,
        provider: &mut impl ProviderCore,
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
    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.get_id(name).is_some()
    }
    #[must_use]
    pub fn get_id(&self, name: &str) -> Option<Id> {
        self.name_to_id.get(name).copied()
    }
    #[must_use]
    pub fn get_name(&self, id: Id) -> Option<&str> {
        self.id_to_name.get(&id).map(|s| &**s)
    }

    // Option:
    //  If we have UUIDs instead, we can just remove the Id from `self`,
    //  as any attempts to resolve that into a path will fail.
    #[allow(clippy::missing_panics_doc)]
    pub fn force_remove(&mut self, document: Id, provider: &mut impl ProviderCore) {
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
pub trait Document {
    fn iter_occurences<'a, I: DocumentPositionWordIter<'a>>(&self) -> I;
}
pub trait DocumentPositionWordIter<'a>: Iterator<Item = WordOccurrence> {}
pub trait DocumentIter<'a, T: Document + 'a>: Iterator<Item = T> {}

/// Allows to get data from the provider.
///
/// Some [`ProviderCore`] implementers might need to be extended with more data to supply all the
/// necessary information.
pub trait Proider: ProviderCore {
    fn documents_with_word<'a, T: Document + 'a, I: DocumentIter<'a, T>>(&'a self, word: &str)
        -> I;
}
/// Allows to insert words and remove occurrences from documents.
pub trait ProviderCore {
    fn insert_word<'a>(&mut self, word: impl Into<Cow<'a, str>>, document: Id);
    fn remove_document(&mut self, document: Id);

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
}
impl Default for Simple {
    fn default() -> Self {
        Self::new()
    }
}
impl ProviderCore for Simple {
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
}
// Simple with read data. If cache doesn't contain the needed word, panic.
// Write about this behaviour in the docs. Make clear you have to add all the ones
// you plan on looking up to the cache.
