# type-walker

This is a toy crate that provides an API to visit the fields and sub-fields of a type with an
`Iterator`-like API. It mimics the kind of traversal done by
[derive-visitor](https://crates.io/crates/derive-visitor), but the iterator-like interface is a lot
more flexible to use.

This comes at the cost of type-level hacks, bit of `unsafe`, and having to work around
borrow-checker limitations.
