[![crates.io version](https://img.shields.io/crates/v/elipdotter)](https://crates.io/crates/elipdotter)
![lines of code](https://img.shields.io/tokei/lines/github/Icelk/elipdotter)
![license](https://img.shields.io/github/license/Icelk/elipdotter)

# Elipdotter

> The forgotten daughter of Elip, inheriting it's minimalism.

Elipdotter is an embeddable, [rusty](https://rust-lang.org) full-text search engine, with fuzzy search and rating of results.
It supports complex queries using `AND`, `OR`, and `NOT` operators with parentheses.

## Kvarn integration

Using the [`kvarn-search`](https://github.com/Icelk/kvarn-search),
you can easily use this search engine in your [Kvarn web server](https://kvarn.org).

# Usage example

See the [source of `kvarn-search`](https://github.com/Icelk/kvarn-search/tree/main/src/)
for a comprehensive example.

The [tests of this crate](https://github.com/Icelk/elipdotter/tree/main/tests/)
contain minimal examples.

# Changelog

## v0.3.2

-   Fix an issue with AND NOT, where some results would disappear when adding the NOT part.

## v0.3.1

-   Removed unwanted debugging.

## v0.3.0

-   Added lossless index for faster query resolution times.
    -   10x better performance at the cost of having all the documents in memory.
-   Fixed parsing issue where `for me` would be parsed as `OR(f, me)`.
-   Fixed issue with AND NOT, where AND didn't find the closest NOT occurrence.
-   Added size method to indices to estimate the memory usage.
-   Improvements to [docs](https://doc.icelk.dev/elipdotter/elipdotter/).

## v0.2.0

-   [Fixed issue](https://github.com/Icelk/elipdotter/commit/7ab071c) where AND NOT queries got erroneous results.
-   [Fixed issue](https://github.com/Icelk/elipdotter/commit/51370f7) with OR queries. Now all occurrences in either of the documents are returned.
-   Major improvements to relevancy of results, by checking more combinations of occurrences within a document. Small performance impact.
-   Text `next-gen` is now matched by the query `nextgen` - words with hyphens are registered as both separate words and one single.
-   Better [docs](https://doc.icelk.dev/elipdotter/elipdotter/).
-   Fewer allocations - less memory usage.

# License

Elipdotter is licensed under the [GNU LGPLv3](COPYING).
All contributions must also be.
