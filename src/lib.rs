#![feature(impl_trait_in_assoc_type)]
#![feature(array_try_map)]

pub use lending_iterator::*;
pub use visitor::*;
pub use walker::*;

/// The lending iterator trait and helpers.
// I define my own instead of using https://docs.rs/lending-iterator/latest/lending_iterator
// because that one doesn't have `inspect`, `chain` or `zip`, and also with nougat I hit
// https://github.com/rust-lang/rust/issues/126519.
pub mod lending_iterator;
pub mod visitor;
pub mod walker;
