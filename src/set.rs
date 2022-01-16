use std::iter::Peekable;

/// Convenience trait for `Iterator<Item = T> -> Iter<T>`.
pub trait Iter<T>: Iterator<Item = T> {}
impl<T, I: Iterator<Item = T>> Iter<T> for I {}

#[derive(Debug)]
pub struct Deduplicate<T, I, F>
where
    I: Iterator<Item = T>,
    F: Fn(T, T) -> T,
{
    iter: Peekable<I>,
    current: Option<T>,
    chooser: F,
}
impl<T, I: Iter<T>, F: Fn(T, T) -> T> Deduplicate<T, I, F> {
    fn new(iter: I, chooser: F) -> Self {
        Self {
            iter: iter.peekable(),
            current: None,
            chooser,
        }
    }
}
impl<T: PartialEq, I: Iter<T>, F: Fn(T, T) -> T> Iterator for Deduplicate<T, I, F> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next = match self.iter.next() {
                Some(next) => next,
                None => return None,
            };

            let peeked = match self.iter.peek() {
                Some(peeked) => peeked,
                None => return Some(next),
            };

            if &next != peeked {
                return Some(self.current.take().unwrap_or(next));
            }
            // UNWRAP: The peeked value is Some.
            let peeked = self.iter.next().unwrap();
            self.current = Some((self.chooser)(next, peeked));
        }
    }
}
/// Removes consecutive duplicate items.
///
/// This works best for sorted iterators (e.g. [`std::collections::BTreeMap::iter`]) as they
/// always have any duplicate items right after each other.
pub fn deduplicate<T: PartialEq, I: Iter<T>>(iter: I) -> Deduplicate<T, I, fn(T, T) -> T> {
    Deduplicate::new(iter, |a, _| a)
}
/// Removes consecutive duplicate items.
///
/// If duplicate items are detected, the `chooser` callback decides which of them to keep.
///
/// This works best for sorted iterators (e.g. [`std::collections::BTreeMap::iter`]) as they
/// always have any duplicate items right after each other.
pub fn deduplicate_by_keep_fn<T: PartialEq, I: Iter<T>, F: Fn(T, T) -> T>(
    iter: I,
    chooser: F,
) -> Deduplicate<T, I, F> {
    Deduplicate::new(iter, chooser)
}

/// Returns an iterator of the items in common between `a` and `b`.
///
/// Both iterators must be sorted.
/// The returned iterator is also sorted.
pub fn intersect<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    iter_set::intersection(deduplicate(a.into_iter()), deduplicate(b.into_iter()))
}
/// Returns an iterator of all the items that occur in either `a` or `b`.
///
/// Both iterators must be sorted.
/// The returned iterator is also sorted.
pub fn union<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    iter_set::union(deduplicate(a.into_iter()), deduplicate(b.into_iter()))
}
/// Returns an iterator of the items in `a` AND NOT in `b`.
///
/// Both iterators must be sorted.
/// The returned iterator is also sorted.
pub fn difference<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    iter_set::difference(deduplicate(a.into_iter()), deduplicate(b.into_iter()))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{difference, intersect, union};

    fn btrees() -> (BTreeSet<&'static str>, BTreeSet<&'static str>) {
        let mut btree1 = BTreeSet::new();
        btree1.insert("hi");
        btree1.insert("and");
        btree1.insert("bye");
        let mut btree2 = BTreeSet::new();
        btree2.insert("Hello");
        btree2.insert("there!");
        btree2.insert("See you!");
        btree2.insert("bye");
        (btree1, btree2)
    }

    #[test]
    fn intersect_1() {
        let (btree1, btree2) = btrees();
        let mut iter = intersect(btree1.iter(), btree2.iter()).copied();
        assert_eq!(iter.next(), Some("bye"));
        assert_eq!(iter.next(), None);
    }
    #[test]
    fn union_1() {
        let (btree1, btree2) = btrees();
        let iter = union(btree1.iter(), btree2.iter()).copied();

        assert!(iter.eq(["Hello", "See you!", "and", "bye", "hi", "there!"]));
    }
    #[test]
    fn difference_1() {
        let (btree1, btree2) = btrees();
        let iter = difference(btree1.iter(), btree2.iter()).copied();

        assert!(iter.eq(["and", "hi"]));
    }
}
