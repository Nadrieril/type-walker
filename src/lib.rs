#![feature(impl_trait_in_assoc_type)]
#![feature(array_try_map)]

pub mod lending_iterator_ext;
pub mod walker;
pub mod zip;

#[doc(inline)]
pub use walker::{TypeWalker, Walkable};

/// Basic types needed to use this crate.
pub mod prelude {
    #[doc(no_inline)]
    pub use crate::lending_iterator_ext::{Either, LendingIteratorExt};
    #[doc(no_inline)]
    pub use crate::walker::{empty_walker, single, TypeWalker, Walkable};
    #[doc(no_inline)]
    pub use crate::zip::{zip_walkables, ZipVisitorMut, ZipWalker};

    #[doc(no_inline)]
    pub use derive_visitor::{Event, VisitorBuilder, VisitorMut};
    #[doc(no_inline)]
    pub use lending_iterator::prelude::Item;
    #[doc(no_inline)]
    #[nougat::gat(Item)]
    pub use lending_iterator::prelude::LendingIterator;
    #[doc(no_inline)]
    pub use std::any::Any;
}
