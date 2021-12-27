use std::cmp::Ordering;
use std::iter::Peekable;
use std::marker::PhantomData;

// Use <https://crates.io/crates/iter-set>?
//
// Make dedupe.

#[derive(Debug)]
pub struct Deduplicate<T, I: Iter<T>> {
    iter: Peekable<I>,
    current: Option<T>,
    _t: PhantomData<T>,
}
impl<T: PartialEq, I: Iter<T>> Iterator for Deduplicate<T, I> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next = self.iter.peek();
            if next.is_none() {
                return self.current.take();
            }
            if next == self.current.as_ref() {
                self.current = self.iter.next();
            } else {
                let current = self.current.take();
                self.current = self.iter.next();
                return current;
            }
        }
    }
}
pub fn deduplicate<T, I: Iter<T>>(iter: I) -> Deduplicate<T, I> {
    Deduplicate {
        iter: iter.peekable(),
        current: None,
        _t: PhantomData,
    }
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

/// Convenience trait for `Iterator<Item = T> -> Iter<T>`.
pub trait Iter<T>: Iterator<Item = T> {}
impl<T, I: Iterator<Item = T>> Iter<T> for I {}

#[derive(Debug)]
pub struct Intersect<T, I1: Iter<T>, I2: Iter<T>> {
    i1: Peekable<I1>,
    i2: Peekable<I2>,
    _t: PhantomData<T>,
}

impl<T, I1: Iter<T>, I2: Iter<T>> Intersect<T, I1, I2> {
    pub fn new(i1: Peekable<I1>, i2: Peekable<I2>) -> Self {
        Self {
            i1,
            i2,
            _t: PhantomData,
        }
    }
}
impl<T: Ord, I1: Iter<T>, I2: Iter<T>> Iterator for Intersect<T, I1, I2> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let (Some(item1), Some(item2)) = (self.i1.peek(), self.i2.peek()) {
                match item1.cmp(item2) {
                    Ordering::Less => self.i1.next(),
                    Ordering::Greater => self.i2.next(),
                    Ordering::Equal => {
                        // i1.next() == i2.next().
                        // Doesn't matter which we return.
                        self.i1.next();
                        return self.i2.next();
                    }
                }
            } else {
                return None;
            };
        }
    }
}
/// `i1` and `i2` must be sorted according to the [`Ord`] implementation of `T`.
pub fn intersect<T: Ord>(
    i1: impl Iterator<Item = T>,
    i2: impl Iterator<Item = T>,
) -> impl Iterator<Item = T> {
    let i1 = i1.peekable();
    let i2 = i2.peekable();
    Intersect::new(i1, i2)
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
