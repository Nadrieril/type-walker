pub use chain::Chain;
pub use filter::Filter;
pub use inspect::Inspect;
pub use zip::Zip;

// GAT hack taken from https://docs.rs/lending-iterator/latest/lending_iterator. With a real GAT we
// can't write the `TypeWalker` trait alias because of a type-checker limitation.
pub trait LendingIterator: Sized
where
    Self: for<'item> LendingIteratorItem<'item>,
{
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
        I: for<'item> LendingIteratorItem<'item, Item = Item<'item, Self>>,
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

/// Hack to express a GAT without GATs.
pub trait LendingIteratorItem<'item, Bounds = &'item Self> {
    type Item;
}

/// Type alias for convenience.
pub type Item<'lt, I> = <I as LendingIteratorItem<'lt>>::Item;

/// The inner workings of `LendingIterator::inspect`.
pub mod inspect {
    use crate::*;

    pub struct Inspect<I, F> {
        pub(super) iter: I,
        pub(super) f: F,
    }

    impl<'item, I: LendingIterator, F> LendingIteratorItem<'item> for Inspect<I, F> {
        type Item = Item<'item, I>;
    }

    impl<I, F> LendingIterator for Inspect<I, F>
    where
        I: LendingIterator,
        F: for<'a> FnMut(&mut Item<'a, Self>),
    {
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

    impl<'item, I: LendingIterator, F> LendingIteratorItem<'item> for Filter<I, F> {
        type Item = Item<'item, I>;
    }

    impl<I, F> LendingIterator for Filter<I, F>
    where
        I: LendingIterator,
        F: for<'a> FnMut(&Item<'a, Self>) -> bool,
    {
        fn next(&mut self) -> Option<Item<'_, Self>> {
            while let Some(next) = self.iter.next() {
                if (self.f)(&next) {
                    return Some(next);
                }
            }
            None
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

    impl<'item, I, J> LendingIteratorItem<'item> for Chain<I, J>
    where
        I: LendingIteratorItem<'item>,
        J: LendingIteratorItem<'item, Item = I::Item>,
    {
        type Item = I::Item;
    }

    impl<I, J> LendingIterator for Chain<I, J>
    where
        I: LendingIterator,
        J: LendingIterator,
        J: for<'item> LendingIteratorItem<'item, Item = Item<'item, I>>,
    {
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

    impl<'item, I, J> LendingIteratorItem<'item> for Zip<I, J>
    where
        I: LendingIteratorItem<'item>,
        J: LendingIteratorItem<'item>,
    {
        type Item = (I::Item, J::Item);
    }

    impl<I, J> LendingIterator for Zip<I, J>
    where
        I: LendingIterator,
        J: LendingIterator,
    {
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

    impl<'item, I, J> LendingIteratorItem<'item> for Either<I, J>
    where
        I: LendingIteratorItem<'item>,
        J: LendingIteratorItem<'item, Item = I::Item>,
    {
        type Item = I::Item;
    }

    impl<I, J> LendingIterator for Either<I, J>
    where
        I: LendingIterator,
        J: LendingIterator,
        J: for<'item> LendingIteratorItem<'item, Item = Item<'item, I>>,
    {
        fn next(&mut self) -> Option<Item<'_, I>> {
            match self {
                Self::Left(l) => l.next(),
                Self::Right(r) => r.next(),
            }
        }
    }
}

#[test]
fn test_simple_lending_iterator() {
    struct RepeatRef<T>(T);
    impl<'item, T> LendingIteratorItem<'item> for RepeatRef<T> {
        type Item = &'item mut T;
    }

    impl<T> LendingIterator for RepeatRef<T> {
        fn next(&mut self) -> Option<Item<'_, Self>> {
            Some(&mut self.0)
        }
    }
}
