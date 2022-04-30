//! A light-weight (2 total dependencies, including descendants)
//! embeddable search engine with typo tolerance, result relevance, and complex queries.
//!
//! If you want *page* relevancy (like [PageRank](https://en.wikipedia.org/wiki/PageRank)),
//! you have to implement it on your own.
//!
//! Also note that you have to provide this library with data and data updates.
//! See [`kvarn-search`](https://github.com/Icelk/kvarn-search) for an example on this.
//!
//! # Iterators
//!
//! When we search for occurrences of a requested word, we get a sorted [`Iterator`].
//! This allows [`query`] to chain iterators together to perform complex queries with few
//! allocations. Only once the client iterates over the occurrences and their relevance do they get
//! processed, ensuring minimal computational expense.
//!
//! Say you want to get the best result, then you can just call [`Iterator::next`] once, and
//! only one occurrence is processed.
#![deny(
    clippy::pedantic,
    unreachable_pub,
    missing_debug_implementations,
    // missing_docs
)]
#![allow(clippy::doc_markdown)]
pub mod index;
pub mod proximity;
pub mod query;
pub mod set;

pub use index::{
    DocumentMap, Lossless as LosslessIndex, LosslessOccurrences as LosslessOccurrencesProvider,
    Simple as SimpleIndex, SimpleOccurences as SimpleOccurrencesProvider,
};
pub use query::{Hit, Part, Query};
