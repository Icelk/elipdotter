use std::iter::Peekable;

/// Convenience trait for `Iterator<Item = T> -> Iter<T>`.
pub trait Iter<T>: Iterator<Item = T> {}
impl<T, I: Iterator<Item = T>> Iter<T> for I {}

#[derive(Debug)]
pub struct Deduplicate<T, I>
where
    I: Iterator<Item = T>,
{
    iter: Peekable<I>,
}
impl<T, I: Iter<T>> Deduplicate<T, I> {
    fn new(iter: I) -> Self {
        Self {
            iter: iter.peekable(),
        }
    }
}
impl<T: PartialEq, I: Iter<T>> Iterator for Deduplicate<T, I> {
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
                return Some(next);
            }
        }
    }
}
/// Removes consecutive duplicate items.
///
/// This works best for sorted iterators (e.g. [`std::collections::BTreeMap::iter`]) as they
/// always have any duplicate items right after each other.
pub fn deduplicate<T: PartialEq, I: Iter<T>>(iter: I) -> Deduplicate<T, I> {
    Deduplicate::new(iter)
}

pub fn intersect<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    iter_set::intersection(deduplicate(a.into_iter()), deduplicate(b.into_iter()))
}
pub fn union<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    iter_set::union(deduplicate(a.into_iter()), deduplicate(b.into_iter()))
}
/// In a AND NOT b
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

    use super::intersect;

    #[test]
    fn intersect_1() {
        let mut btree1 = BTreeSet::new();
        btree1.insert("hi");
        btree1.insert("and");
        btree1.insert("bye");
        let mut btree2 = BTreeSet::new();
        btree2.insert("Hello");
        btree2.insert("there!");
        btree2.insert("See you!");
        btree2.insert("bye");
        let mut iter = intersect(btree1.iter(), btree2.iter()).copied();
        assert_eq!(iter.next(), Some("bye"));
        assert_eq!(iter.next(), None);
    }
}
