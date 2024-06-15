use higher_kinded_types::ForLifetime;
use std::marker::PhantomData;

pub use chain::Chain;
pub use empty::Empty;
pub use filter::Filter;
pub use inspect::Inspect;
pub use zip::Zip;

// GAT hack taken from https://docs.rs/lending-iterator/latest/lending_iterator. With a real GAT we
// can't write the `TypeWalker` trait alias because of a type-checker limitation.
#[nougat::gat]
pub trait LendingIterator: Sized {
    type Item<'item>
    where
        Self: 'item;

    fn next(&mut self) -> Option<Item<'_, Self>>;

    /// Like `Iterator::inspect`.
    fn inspect<F: for<'a> FnMut(&mut Item<'a, Self>)>(self, f: F) -> Inspect<Self, F> {
        Inspect { iter: self, f }
    }

    /// Like `Iterator::filter`.
    fn filter<F: for<'a> FnMut(&Item<'a, Self>) -> bool>(self, f: F) -> Filter<Self, F> {
        Filter { iter: self, f }
    }

    /// Like `Iterator::chain`.
    fn chain<I: LendingIterator>(self, other: I) -> Chain<Self, I>
    where
        I: for<'item> LendingIterator<Item<'item> = Item<'item, Self>>,
    {
        Chain {
            first: Some(self),
            second: Some(other),
        }
    }

    /// Like `Iterator::zip`.
    fn zip<I: LendingIterator>(self, other: I) -> Zip<Self, I> {
        Zip {
            first: self,
            second: other,
        }
    }
}

/// Type alias for convenience.
pub type Item<'item, I> = nougat::Gat!(<I as LendingIterator>::Item<'item>);

/// The inner workings of `LendingIterator::inspect`.
pub mod inspect {
    use crate::*;

    pub struct Inspect<I, F> {
        pub(super) iter: I,
        pub(super) f: F,
    }

    #[nougat::gat]
    impl<I, F> LendingIterator for Inspect<I, F>
    where
        I: LendingIterator,
        F: for<'a> FnMut(&mut Item<'a, I>),
    {
        type Item<'item> = Item<'item, I>;
        fn next(&mut self) -> Option<Item<'_, Self>> {
            let mut next = self.iter.next();
            if let Some(next) = next.as_mut() {
                (self.f)(next)
            }
            next
        }
    }
}

/// The inner workings of `LendingIterator::filter`.
pub mod filter {
    use crate::*;

    pub struct Filter<I, F> {
        pub(super) iter: I,
        pub(super) f: F,
    }

    #[nougat::gat]
    impl<I, F> LendingIterator for Filter<I, F>
    where
        I: LendingIterator,
        F: for<'a> FnMut(&Item<'a, I>) -> bool,
    {
        type Item<'item> = Item<'item, I>;
        fn next(&mut self) -> Option<Item<'_, Self>> {
            use polonius_the_crab::*;
            let mut this = self;
            polonius_loop!(|this| -> Option<Item<'polonius, Self>> {
                let next = polonius_try!(this.iter.next());
                if (this.f)(&next) {
                    polonius_return!(Some(next));
                }
            })
        }
    }
}

/// The inner workings of `LendingIterator::chain`.
pub mod chain {
    use crate::*;

    pub struct Chain<I, J> {
        pub(super) first: Option<I>,
        pub(super) second: Option<J>,
    }

    #[nougat::gat]
    impl<I, J> LendingIterator for Chain<I, J>
    where
        I: LendingIterator,
        J: LendingIterator,
        J: for<'i> LendingIterator<Item<'i> = Item<'i, I>>,
    {
        type Item<'item> = Item<'item, I>;
        fn next(&mut self) -> Option<Item<'_, I>> {
            use polonius_the_crab::*;
            let mut this = self;
            polonius!(|this| -> Option<Item<'polonius, I>> {
                if let Some(first) = &mut this.first {
                    if let Some(next) = first.next() {
                        polonius_return!(Some(next));
                    }
                }
            });
            this.first = None;
            polonius!(|this| -> Option<Item<'polonius, I>> {
                if let Some(second) = &mut this.second {
                    if let Some(next) = second.next() {
                        polonius_return!(Some(next));
                    }
                }
            });
            this.second = None;
            None
        }
    }
}

/// The inner workings of `LendingIterator::zip`.
pub mod zip {
    use crate::*;

    pub struct Zip<I, J> {
        pub(super) first: I,
        pub(super) second: J,
    }

    #[nougat::gat]
    impl<I, J> LendingIterator for Zip<I, J>
    where
        I: LendingIterator,
        J: LendingIterator,
    {
        type Item<'item> = (Item<'item, I>, Item<'item, J>);
        fn next(&mut self) -> Option<Item<'_, Self>> {
            let first = self.first.next()?;
            let second = self.second.next()?;
            Some((first, second))
        }
    }
}

pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// The inner workings of `Either`.
pub mod either {
    use crate::*;

    #[nougat::gat]
    impl<I, J> LendingIterator for Either<I, J>
    where
        I: LendingIterator,
        J: LendingIterator,
        J: for<'i> LendingIterator<Item<'i> = Item<'i, I>>,
    {
        type Item<'item> = Item<'item, I>;
        fn next(&mut self) -> Option<Item<'_, I>> {
            match self {
                Self::Left(l) => l.next(),
                Self::Right(r) => r.next(),
            }
        }
    }
}

/// Empty iterator.
pub fn empty<HKT: ForLifetime>() -> Empty<HKT> {
    Empty(PhantomData)
}

/// The inner workings of `empty`.
pub mod empty {
    use higher_kinded_types::ForLifetime;
    use std::marker::PhantomData;

    use crate::*;

    pub struct Empty<HKT>(pub(super) PhantomData<HKT>);

    type HKTOf<'lt, HKT> = <HKT as ForLifetime>::Of<'lt>;

    #[nougat::gat]
    impl<HKT: ForLifetime> LendingIterator for Empty<HKT> {
        type Item<'item> = HKTOf<HKT, 'item>;
        fn next(&mut self) -> Option<Item<'_, Self>> {
            None
        }
    }
}

/// Implementations on std types.
mod std_impls {
    use crate::{Item, LendingIterator, LendingIteratorඞItem};

    #[nougat::gat]
    impl<I: LendingIterator> LendingIterator for Box<I> {
        type Item<'item> = Item<'item, I>;
        fn next(&mut self) -> Option<Item<'_, Self>> {
            (**self).next()
        }
    }
}

#[test]
fn test_simple_iterator() {
    struct RepeatRef<T>(T);

    #[nougat::gat]
    impl<T> LendingIterator for RepeatRef<T> {
        type Item<'item> = &'item mut T;
        fn next(&mut self) -> Option<Item<'_, Self>> {
            Some(&mut self.0)
        }
    }
}

#[test]
// This one isn't possible with a normal gat-based lening iterator because of known type system
// limitations.
fn test_non_static_iterator() {
    struct RepeatRef<'a, T>(&'a mut T);

    #[nougat::gat]
    impl<'a, T> LendingIterator for RepeatRef<'a, T> {
        type Item<'item> = &'item mut T;
        fn next(&mut self) -> Option<Item<'_, Self>> {
            Some(&mut *self.0)
        }
    }
}
