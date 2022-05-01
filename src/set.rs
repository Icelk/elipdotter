//! Set operations on ordered iterators.
//! These are the fundamental join operations of the search engine.
//!
//! These are provided by [`iter_set`], except [`progressive`] and [`deduplicate`],
//! which are written by be.
use std::cmp::Ordering;
use std::fmt::Debug;
use std::iter::Peekable;
use std::mem;

use iter_set::Inclusion;

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
impl<T, I: Iterator<Item = T>, F: Fn(T, T) -> T> Deduplicate<T, I, F> {
    fn new(iter: I, chooser: F) -> Self {
        Self {
            iter: iter.peekable(),
            current: None,
            chooser,
        }
    }
}
impl<T: PartialEq, I: Iterator<Item = T>, F: Fn(T, T) -> T> Iterator for Deduplicate<T, I, F> {
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
///
/// All the iterators used within elipdotter are sorted.
pub fn deduplicate<T: PartialEq, I: Iterator<Item = T>>(iter: I) -> Deduplicate<T, I, fn(T, T) -> T> {
    Deduplicate::new(iter, |a, _| a)
}
/// Removes consecutive duplicate items.
///
/// If duplicate items are detected, the `chooser` callback decides which of them to keep.
///
/// This works best for sorted iterators (e.g. [`std::collections::BTreeMap::iter`]) as they
/// always have any duplicate items right after each other.
pub fn deduplicate_by_keep_fn<T: PartialEq, I: Iterator<Item = T>, F: Fn(T, T) -> T>(
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

struct Progressive<
    T: Clone,
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
    C: FnMut(&mut T, &mut T) -> core::cmp::Ordering,
    M: FnMut(&T, &T) -> core::cmp::Ordering,
> {
    l: L,
    r: R,
    matches: M,
    comparison: C,
    minimize_dist_right: Option<fn(&T, &T) -> usize>,
    l_next: Option<T>,
    r_next: Option<T>,
    l_peek: Option<T>,
    r_peek: Option<T>,
}
impl<
        T: Clone,
        L: Iterator<Item = T>,
        R: Iterator<Item = T>,
        C: FnMut(&mut T, &mut T) -> core::cmp::Ordering,
        M: FnMut(&T, &T) -> core::cmp::Ordering,
    > Progressive<T, L, R, C, M>
{
    fn next_l(&mut self) {
        mem::swap(&mut self.l_next, &mut self.l_peek);
        self.l_peek = self.l.next();
    }
    fn next_r(&mut self) {
        mem::swap(&mut self.r_next, &mut self.r_peek);
        self.r_peek = self.r.next();
    }
}
impl<
        T: Clone,
        L: Iterator<Item = T>,
        R: Iterator<Item = T>,
        C: FnMut(&mut T, &mut T) -> core::cmp::Ordering,
        M: FnMut(&T, &T) -> core::cmp::Ordering,
    > Iterator for Progressive<T, L, R, C, M>
{
    type Item = Inclusion<T>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match (self.l_next.take(), self.r_next.take()) {
                (Some(l), Some(r)) => match (self.matches)(&l, &r) {
                    Ordering::Less => {
                        let l = Inclusion::Left(l);
                        self.r_next = Some(r);
                        self.next_l();
                        return Some(l);
                    }
                    Ordering::Equal => {
                        self.l_next = Some(l);
                        self.r_next = Some(r);
                    }
                    Ordering::Greater => {
                        let r = Inclusion::Right(r);
                        self.l_next = Some(l);
                        self.next_r();
                        return Some(r);
                    }
                },
                _ => return None,
            }

            if self.r_peek.is_none() {
                let ret = Inclusion::Both(self.l_next.take()?, self.r_next.clone()?);
                self.next_l();
                return Some(ret);
            }
            if self.l_peek.is_none() {
                let ret = Inclusion::Both(self.l_next.clone()?, self.r_next.take()?);
                self.next_r();
                return Some(ret);
            }

            // If `self.r_peek` and `self.l_peek` are both some, these must be Some. It's a logic error
            // otherwise.
            let left = self.l_next.as_mut().unwrap();
            let right = self.r_next.as_mut().unwrap();
            let cmp = (self.comparison)(left, right);
            let advance_right = cmp == Ordering::Greater;
            // If dist between left and right is less on next iter, iterate right to get closer.
            if let Some(minimize_dist_right) = self.minimize_dist_right {
                if advance_right {
                    let dist = minimize_dist_right(left, right);
                    let peek_dist = if let Some(right) = &self.r_peek {
                        if (self.matches)(left, right) == Ordering::Equal {
                            Some(minimize_dist_right(left, right))
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    // The == part of <= is really important, as we can have duplicates.
                    if peek_dist.map_or(false, |peek_dist| peek_dist <= dist) {
                        self.next_r();
                        continue;
                    }
                    // Now the NOT (right) is as close as possible. Even if it's behind, take the
                    // next AND (left) and check it. Else, the current NOT will not be checked against.
                    let ret = Inclusion::Both(left.clone(), right.clone());
                    self.next_l();
                    return Some(ret);
                }
            }
            let ret = Inclusion::Both(left.clone(), right.clone());
            if advance_right {
                self.next_r();
            } else {
                self.next_l();
            };
            return Some(ret);
        }
    }
}
/// Like [`iter_set::classify`] but when we get two "equal" from `matches`, we let one of those
/// stay in the "cache" to match future ones. The last one or the greatest one according to
/// `comparison` stays.
///
/// If `minimize_dist_right` is [`Some`], the algorithm will only return
/// [`Inclusion::Both`] once `b` is close to `a` as possible.
/// It should return the distance between the two points (using the same algorithm as `comparison`).
/// This is very useful when doing `AND NOT` operations. Set it to [`None`] otherwise.
pub fn progressive<T, L, R, C, M>(
    a: L,
    b: R,
    comparison: C,
    matches: M,
    minimize_dist_right: Option<fn(&T, &T) -> usize>,
) -> impl Iterator<Item = Inclusion<T>>
where
    T: Clone,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    C: FnMut(&mut T, &mut T) -> core::cmp::Ordering,
    M: FnMut(&T, &T) -> core::cmp::Ordering,
{
    let mut l = a.into_iter();
    let mut r = b.into_iter();
    Progressive {
        comparison,
        matches,
        minimize_dist_right,
        l_next: l.next(),
        r_next: r.next(),
        l_peek: l.next(),
        r_peek: r.next(),
        l,
        r,
    }
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
