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

# Todo

-   [ ] Remove the `.collect::<BTreeSet<_>>`s after [`proximate_words`](https://docs.rs/elipdotter/latest/elipdotter/proximity/fn.proximate_words.html)
-   [x] Remove the set in AND NOT queries
-   [ ] for `next-generation`, make the whole stack (index + find occurrences) recognize `next`, `generation`, `nextgeneration`.
        This enables alternative spellings to give matches.

# License

Elipdotter is licensed under the [GNU LGPLv3](COPYING).
All contributions must also be.
