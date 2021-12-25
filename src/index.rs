use std::collections::{BTreeMap, HashMap};
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
    document_to_id: HashMap<String, Id>,
    id_to_document: BTreeMap<Id, String>,
}
impl DocumentMap {
    pub fn new() -> Self {
        Self {
            document_to_id: HashMap::new(),
            id_to_document: BTreeMap::new(),
        }
    }
    #[allow(clippy::missing_panics_doc)]
    pub fn insert(&mut self, document: impl Into<String>) {
        let document = document.into();
        if self.contains(&document) {
            return;
        }

        let id = self.get_first();

        self.document_to_id.insert(document.clone(), id);
        let old_doc = self.id_to_document.insert(id, document);
        assert_eq!(old_doc, None);
    }
    fn get_first(&self) -> Id {
        let mut last = 0;
        for id in self.id_to_document.keys() {
            if id.inner() != last && id.inner() != last + 1 {
                return Id::new(last + 1);
            }
            last = id.inner();
        }
        Id::new(last + 1)
    }
    #[must_use]
    pub fn contains(&self, document: &str) -> bool {
        self.get_id(document).is_some()
    }
    #[must_use]
    pub fn get_id(&self, document: &str) -> Option<Id> {
        self.document_to_id.get(document).copied()
    }
    #[must_use]
    pub fn get_document(&self, id: Id) -> Option<&str> {
        self.id_to_document.get(&id).map(|s| &**s)
    }
}

impl Default for DocumentMap {
    fn default() -> Self {
        Self::new()
    }
}

// `TODO`: Use this to give detailed data (docs with all words? Exactly as in Lossless index, but
// processed when the iterator is called)
//
// Then, with the [`DocumentMap`], give it that.
pub trait Provider {
    fn insert_word(&mut self, word: &str, document: Id);
    fn documents_with_word<'a, I: Iterator<Item = &'a str>>(&'a self, word: &str) -> I;
}

#[derive(Debug)]
pub struct Index<I: Provider> {
    index: I,
    doc_map: DocumentMap,
}
impl<I: Provider> Index<I> {
    pub fn insert(&mut self, name: impl Into<String>, data: impl AsRef<str>) {
        self.doc_map.insert(name);
    }
}
