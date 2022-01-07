#![deny(
    clippy::pedantic,
    unreachable_pub,
    missing_debug_implementations,
    // missing_docs
)]
pub mod index;
pub mod proximity;
pub mod query;
pub mod set;

pub use index::{
    DocumentMap, Simple as SimpleIndex, SimpleOccurences as SimpleIndexOccurenceProvider,
};
pub use query::{Hit, Part, Query};
