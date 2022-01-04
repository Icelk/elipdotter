//! # Big O notation reference
//!
//! `O(1) < O(log n) < O(log n * log n) < O(sqrt(n)) < O(n) < O(n * log n) < O(n^1.1) < O(n²) < O(n³) < O(2^n)`
//!
//! `O(sqrt(n))` is true for all `sqrt(n^m)` where `0<m<1`.
//!
//! Since `O(log n)` is very close to `O(1)`,
//! `O(log n * log n)` is also and
//! `O(n * log n)` is very close to `O(n)`.

use std::cmp;
use std::collections::{btree_map, btree_set, BTreeMap, BTreeSet, HashMap};
use std::fmt::{Debug, Display};
use std::iter::{Copied, Map};
use std::sync::{Arc, Mutex};

use crate::proximity;

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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Occurence {
    start: usize,
    document_id: Id,
}
impl Occurence {
    fn new(pos: usize, document_id: Id) -> Self {
        Self {
            start: pos,
            document_id,
        }
    }
    #[must_use]
    pub fn start(&self) -> usize {
        self.start
    }
    #[must_use]
    pub fn id(&self) -> Id {
        self.document_id
    }
}
/// If [`Occurence`] is part of an AND, these can be associated to tell where the other parts of
/// the AND chain are.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConditionalOccurrence {
    start: usize,
}
impl ConditionalOccurrence {
    pub(crate) fn new(start: usize) -> Self {
        Self { start }
    }
    /// Get the conditional occurrence's start.
    #[must_use]
    pub fn start(&self) -> usize {
        self.start
    }
}

#[derive(Clone, Hash)]
#[repr(transparent)]
pub struct Alphanumeral<T: ?Sized>(T);
impl<T> Alphanumeral<T> {
    pub fn new(s: T) -> Self {
        Self(s)
    }
}
impl<T: AsRef<str>> From<T> for Alphanumeral<T> {
    fn from(v: T) -> Self {
        Self::new(v)
    }
}
impl<T: AsRef<str>> Alphanumeral<T> {
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

/// Needed to index [custom struct](Alphanumeral) in maps.
/// We have to have the same type, so this acts as both the borrowed and owned.
pub struct StrPtr {
    s: *const str,
    drop: bool,
}
impl StrPtr {
    /// # Safety
    ///
    /// `s` must be valid for the lifetime of this object.
    ///
    /// If `drop` is true, we must also own `s`.
    unsafe fn new(s: &str, drop: bool) -> Self {
        Self { s, drop }
    }
    /// # Safety
    ///
    /// `s` must be valid for the lifetime of this object.
    unsafe fn sref<'a>(s: &'a str) -> Self
    where
        Self: 'a,
    {
        // Since `drop` is false, we don't care about ownership.
        Self::new(s, false)
    }
    fn owned(s: impl Into<Box<str>>) -> Self {
        let s = std::mem::ManuallyDrop::new(s.into());
        // SAFETY: Since we have the ownership and used `ManuallyDrop`,
        // the memory will never drop.
        // We have to drop it, and it's valid until we do so.
        unsafe { Self::new(&*s, true) }
    }
    fn as_mut(&self) -> *mut str {
        self.s as *mut _
    }
}
impl Drop for StrPtr {
    fn drop(&mut self) {
        if self.drop {
            // SAFETY: Upheld by caller.
            unsafe { (self.as_mut()).drop_in_place() }
        }
    }
}
impl AsRef<str> for StrPtr {
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

pub(crate) type AlphanumRef = Alphanumeral<StrPtr>;

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
pub trait Provider<'a> {
    type DocumentIter: Iterator<Item = Id> + ExactSizeIterator + 'a;
    type WordIter: Iterator<Item = &'a AlphanumRef> + 'a;
    type WordFilteredIter: Iterator<Item = &'a AlphanumRef> + 'a;

    fn insert_word(&mut self, word: impl AsRef<str>, document: Id);
    fn remove_document(&mut self, document: Id);
    fn contains_word(&self, word: impl AsRef<str>, document: Id) -> bool;
    fn documents_with_word(&'a self, word: impl AsRef<str>) -> Option<Self::DocumentIter>;

    fn word_count_upper_limit(&self) -> usize;
    fn words(&'a self) -> Self::WordIter;
    fn words_starting_with(&'a self, c: char) -> Self::WordFilteredIter;

    fn word_proximity_threshold(&self) -> f64;

    /// Only adds words which are alphanumeric.
    fn digest_document(&mut self, id: Id, content: &str) {
        for word in content.split(word_pattern) {
            if word.is_empty() {
                continue;
            }
            // Word must be alphanumeric to be added.
            if word.contains(|c: char| !c.is_alphanumeric()) {
                continue;
            }

            self.insert_word(word, id);
        }
    }
}
pub trait OccurenceProvider<'a> {
    type Iter: Iterator<Item = Occurence> + 'a;
    fn occurrences_of_word(&'a self, word: &'a str) -> Option<Self::Iter>;
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
    pub fn documents(&self) -> Copied<btree_set::Iter<'_, Id>> {
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
    words: BTreeMap<AlphanumRef, SimpleDocRef>,
    proximity_threshold: f64,
}
impl Simple {
    /// `proximity_threshold` is the threshold where alike words are also accepted.
    /// It uses the range [0..1], where values nearer 0 allow more words.
    ///
    /// The default is `0.9`.
    pub fn new(proximity_threshold: f64) -> Self {
        Self {
            words: BTreeMap::new(),
            proximity_threshold,
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
/// [`Self::new`] with `proximity_threshold` set to `0.9`.
impl Default for Simple {
    fn default() -> Self {
        Self::new(0.9)
    }
}
type FirstTy<'a> = fn((&'a AlphanumRef, &'a SimpleDocRef)) -> &'a AlphanumRef;
impl<'a> Provider<'a> for Simple {
    type DocumentIter = Copied<btree_set::Iter<'a, Id>>;
    type WordIter = btree_map::Keys<'a, AlphanumRef, SimpleDocRef>;
    type WordFilteredIter = Map<btree_map::Range<'a, AlphanumRef, SimpleDocRef>, FirstTy<'a>>;

    /// O(log n log n)
    fn insert_word(&mut self, word: impl AsRef<str>, document: Id) {
        let word = word.as_ref();
        // SAFETY: We only use `StrPtr` in the current scope.
        let ptr = unsafe { StrPtr::sref(word) };
        if let Some(doc_ref) = self.words.get_mut(&Alphanumeral::new(ptr)) {
            doc_ref.insert(document);
        } else {
            let mut doc_ref = SimpleDocRef::new();
            doc_ref.insert(document);
            let word = Alphanumeral::new(word).chars().collect::<String>();
            let ptr = StrPtr::owned(word);
            self.words.insert(Alphanumeral::new(ptr), doc_ref);
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
            .map(SimpleDocRef::documents)
    }

    fn word_count_upper_limit(&self) -> usize {
        self.words.len()
    }
    fn words(&'a self) -> Self::WordIter {
        self.words.keys()
    }
    fn words_starting_with(&'a self, c: char) -> Self::WordFilteredIter {
        let s1 = String::from(c);
        let ptr1 = StrPtr::owned(s1);
        let mut s2 = String::from(c);
        s2.push(char::MAX);
        let ptr2 = StrPtr::owned(s2);

        self.words
            .range(Alphanumeral::new(ptr1)..Alphanumeral::new(ptr2))
            .map(|(k, _v)| k)
    }

    fn word_proximity_threshold(&self) -> f64 {
        self.proximity_threshold
    }
}
fn word_pattern(c: char) -> bool {
    c.is_ascii_whitespace() || c.is_ascii_punctuation()
}
#[derive(Debug)]
pub struct SimpleOccurrencesIter<'a, I> {
    iter: I,
    words: BTreeSet<&'a AlphanumRef>,

    document_contents: &'a HashMap<Id, Arc<String>>,

    #[allow(clippy::type_complexity)] // That's not complex.
    current_doc: Option<(std::str::Split<'a, fn(char) -> bool>, Id)>,
    current_pos: usize,
    current_doc_matched: bool,

    missing: &'a Mutex<Vec<Id>>,
}
impl<'a, I: Iterator<Item = Id>> SimpleOccurrencesIter<'a, I> {
    fn new(
        iter: I,
        words: BTreeSet<&'a AlphanumRef>,
        document_contents: &'a HashMap<Id, Arc<String>>,
        missing: &'a Mutex<Vec<Id>>,
    ) -> Self {
        Self {
            iter,
            words,
            document_contents,
            current_doc: None,
            current_pos: 0,
            current_doc_matched: false,
            missing,
        }
    }
}
impl<'a, I: Iterator<Item = Id>> Iterator for SimpleOccurrencesIter<'a, I> {
    type Item = Occurence;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((doc_iter, doc_id)) = &mut self.current_doc {
            for doc in doc_iter {
                let start = self.current_pos;
                self.current_pos += doc.len() + 1;
                // SAFETY: We only use it in this scope.
                let doc_ptr = unsafe { StrPtr::sref(doc) };
                let doc_ptr = Alphanumeral::new(doc_ptr);

                let doc = Alphanumeral::new(doc);
                if doc.chars().next().is_none() {
                    continue;
                }
                if self.words.contains(&doc_ptr) {
                    self.current_doc_matched = true;
                    return Some(Occurence::new(start, *doc_id));
                }
            }

            if !self.current_doc_matched {
                let mut missing = self.missing.lock().expect(
                    "lock is poisoned, other thread panicked.\
                    This should anyway not be accessed from multiple threads simultaneously",
                );
                missing.push(*doc_id);
            }
        }

        let next_doc = self.iter.next()?;
        let contents = if let Some(c) = self.document_contents.get(&next_doc) {
            c
        } else {
            failed_to_find_document_in_provided_documents()
        };
        self.current_doc = Some((contents.split(word_pattern), next_doc));
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
pub struct SimpleOccurences<'a> {
    index: &'a Simple,
    document_contents: HashMap<Id, Arc<String>>,

    missing: Mutex<Vec<Id>>,
}
/// # Panics
///
/// Using the [`OccurenceProvider::occurrences_of_word`] may panic, if not all documents returned
/// from [`Provider::documents_with_word`]. If a document doesn't exist, still [`Self::add_document`],
/// but with an empty [`String`].
impl<'a> SimpleOccurences<'a> {
    pub fn new(index: &'a Simple) -> Self {
        Self {
            index,
            document_contents: HashMap::new(),
            missing: Mutex::new(Vec::new()),
        }
    }
    pub fn add_document(&mut self, id: Id, content: Arc<String>) {
        self.document_contents.insert(id, content);
    }
}
impl<'a> OccurenceProvider<'a> for SimpleOccurences<'a> {
    type Iter = SimpleOccurrencesIter<'a, Copied<btree_set::Iter<'a, Id>>>;
    fn occurrences_of_word(&'a self, word: &'a str) -> Option<Self::Iter> {
        // SAFETY: We only use `StrPtr` in the current scope.
        let ptr = unsafe { StrPtr::sref(word) };
        let doc_ref = self.index.words.get(&Alphanumeral::new(ptr))?;
        let words = proximity::proximate_words(word, self.index).collect();
        Some(SimpleOccurrencesIter::new(
            doc_ref.docs.iter().copied(),
            words,
            &self.document_contents,
            &self.missing,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Alphanumeral, DocumentMap, Id, Occurence, OccurenceProvider, Provider, Simple,
        SimpleOccurences,
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
    fn occurences() {
        let mut doc_map = DocumentMap::new();
        let mut index = Simple::default();
        doc_map.insert("doc1", doc1(), &mut index);
        doc_map.insert("doc3", doc2(), &mut index);

        assert!(index.contains_word("lorem", doc_map.get_id("doc1").unwrap()));
        assert!(index.contains_word("lorem", doc_map.get_id("doc3").unwrap()));
        assert_eq!(doc_map.get_id("doc3"), Some(Id::new(1)));
        assert_eq!(doc_map.get_id("doc2"), None);

        let mut simple_provider = SimpleOccurences::new(&index);
        simple_provider.add_document(doc_map.get_id("doc1").unwrap(), doc1().to_string().into());
        simple_provider.add_document(doc_map.get_id("doc3").unwrap(), doc2().to_string().into());

        let mut occurrences = simple_provider.occurrences_of_word("lorem").unwrap();
        // Same problem here as above
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(0, doc_map.get_id("doc1").unwrap()))
        );
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(875, doc_map.get_id("doc1").unwrap()))
        );
        assert_eq!(
            occurrences.next(),
            Some(Occurence::new(0, doc_map.get_id("doc3").unwrap()))
        );
        assert_eq!(occurrences.next(), None,);
    }
}
