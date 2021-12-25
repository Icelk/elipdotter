#![deny(
    clippy::pedantic,
    unreachable_pub,
    missing_debug_implementations,
    // missing_docs
)]
pub mod query;
pub mod index;

// `TODO`: Intersect & union sets of responses
