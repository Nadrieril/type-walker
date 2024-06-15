#![feature(impl_trait_in_assoc_type)]

use lending_iterator::*;
use visitor::*;

/// The lending iterator trait and helpers.
// I define my own instead of using an existing one because the existing ones don't define the
// `Item` type separately.
pub mod lending_iterator {
    pub use chain::Chain;
    pub use filter::Filter;
    pub use inspect::Inspect;
    pub use zip::Zip;

    // We split the trait in two to avoid the `Self: 'a` bound. If the bound is there we can't
    // write the `TypeWalker` trait alias because the `Self: 'a` bound makes the `for<'a>`
    // constraint impossible to satisfy.
    // This makes it impossible to yield items that borrow directly from `self`. That's
    // unfortunate, but we don't need that for our visitors.
    pub trait LendingIteratorItem {
        type Item<'item>;
    }

    pub trait LendingIterator: LendingIteratorItem + Sized {
        fn next(&mut self) -> Option<Self::Item<'_>>;

        /// Like `Iterator::inspect`.
        fn inspect<F: for<'a> FnMut(&mut Self::Item<'a>)>(self, f: F) -> Inspect<Self, F> {
            Inspect { iter: self, f }
        }

        /// Like `Iterator::filter`.
        fn filter<F: for<'a> FnMut(&Self::Item<'a>) -> bool>(self, f: F) -> Filter<Self, F> {
            Filter { iter: self, f }
        }

        /// Like `Iterator::chain`.
        fn chain<I: LendingIterator>(self, other: I) -> Chain<Self, I>
        where
            I: for<'item> LendingIteratorItem<Item<'item> = Self::Item<'item>>,
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

    /// The inner workings of `LendingIterator::inspect`.
    pub mod inspect {
        use crate::*;

        pub struct Inspect<I, F> {
            pub(super) iter: I,
            pub(super) f: F,
        }

        impl<I: LendingIterator, F> LendingIteratorItem for Inspect<I, F> {
            type Item<'item> = I::Item<'item>;
        }

        impl<I, F> LendingIterator for Inspect<I, F>
        where
            I: LendingIterator,
            F: for<'a> FnMut(&mut Self::Item<'a>),
        {
            fn next(&mut self) -> Option<Self::Item<'_>> {
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

        impl<I: LendingIterator, F> LendingIteratorItem for Filter<I, F> {
            type Item<'item> = <I as LendingIteratorItem>::Item<'item>;
        }

        impl<I, F> LendingIterator for Filter<I, F>
        where
            I: LendingIterator,
            F: for<'a> FnMut(&Self::Item<'a>) -> bool,
        {
            fn next(&mut self) -> Option<Self::Item<'_>> {
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

        impl<I, J> LendingIteratorItem for Chain<I, J>
        where
            I: LendingIteratorItem,
            J: for<'item> LendingIteratorItem<Item<'item> = I::Item<'item>>,
        {
            type Item<'item> = I::Item<'item>;
        }

        impl<I, J> LendingIterator for Chain<I, J>
        where
            I: LendingIterator,
            J: LendingIterator,
            J: for<'item> LendingIteratorItem<Item<'item> = I::Item<'item>>,
        {
            fn next(&mut self) -> Option<Self::Item<'_>> {
                if let Some(first) = &mut self.first {
                    if let Some(next) = first.next() {
                        return Some(next);
                    } else {
                        self.first = None;
                    }
                }
                if let Some(second) = &mut self.second {
                    if let Some(next) = second.next() {
                        return Some(next);
                    } else {
                        self.second = None;
                    }
                }
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

        impl<I, J> LendingIteratorItem for Zip<I, J>
        where
            I: LendingIteratorItem,
            J: LendingIteratorItem,
        {
            type Item<'item> = (I::Item<'item>, J::Item<'item>);
        }

        impl<I, J> LendingIterator for Zip<I, J>
        where
            I: LendingIterator,
            J: LendingIterator,
        {
            fn next(&mut self) -> Option<Self::Item<'_>> {
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

        impl<I, J> LendingIteratorItem for Either<I, J>
        where
            I: LendingIteratorItem,
        {
            type Item<'item> = I::Item<'item>;
        }

        impl<I, J> LendingIterator for Either<I, J>
        where
            I: LendingIterator,
            J: LendingIterator,
            J: for<'item> LendingIteratorItem<
                Item<'item> = <I as LendingIteratorItem>::Item<'item>,
            >,
        {
            fn next(&mut self) -> Option<Self::Item<'_>> {
                match self {
                    Self::Left(l) => l.next(),
                    Self::Right(r) => r.next(),
                }
            }
        }
    }
}

/// The visitor crate would provide these definitions.
pub mod visitor {
    use crate::lending_iterator::inspect::Inspect;
    use crate::*;
    use std::any::Any;

    /// A type that can be visited.
    pub trait Walkable {
        type Walker<'a>: TypeWalker
        where
            Self: 'a;
        fn walk<'a>(&'a mut self) -> Self::Walker<'a>;
    }

    #[derive(Debug, Clone, Copy)]
    pub enum Event {
        Enter,
        Exit,
    }

    /// A type visitor.
    /// This is a trait alias for the right kind of lending iterator, with extra provided methods
    /// for convenience.
    pub trait TypeWalker:
        Sized
        + LendingIterator
        + for<'item> LendingIteratorItem<Item<'item> = (&'item mut dyn Any, Event)>
    {
        /// Returns the next value of type `T`.
        fn next_t<T: 'static>(&mut self) -> Option<(&mut T, Event)> {
            while let Some((next, e)) = self.next() {
                if let Some(next) = next.downcast_mut::<T>() {
                    return Some((next, e));
                }
            }
            None
        }

        /// Provided method that calls `f` on each visited item of type `T`. Returns a new visitor
        /// that visits on the same items (of course `f` may have modified them in flight).
        fn inspect_t<T: 'static, F: FnMut(&mut T, Event)>(
            self,
            mut f: F,
        ) -> Inspect<Self, impl FnMut(&mut (&mut dyn Any, Event))> {
            self.inspect(move |(next, event): &mut (&mut dyn Any, Event)| {
                if let Some(next_t) = (*next).downcast_mut::<T>() {
                    f(next_t, *event)
                }
            })
        }

        /// Runs to completion. Convenient in combination with `inspect_t`.
        fn run_to_completion(&mut self) {
            loop {
                let next = self.next();
                if next.is_none() {
                    break;
                }
            }
        }
    }
    /// Blanket impl for all lending iterators of the right type.
    // This is the reason we can't use a clean GAT-based lending iterator: rustc forces us to add a
    // `where Self: 'item` bound to the GAT, which means this `for<'item>` bound cannot be
    // satistied. If we could write `for<'item such that Self: 'item>` we'd be good, but I don't
    // know of a way to express that, even with hacks.
    impl<T> TypeWalker for T
    where
        T: LendingIterator,
        T: for<'item> LendingIteratorItem<Item<'item> = (&'item mut dyn Any, Event)>,
    {
    }

    /// Trait for the common case of types that are walked by yielding `(self, Enter)`, walking
    /// over the contents, and finally yielding `(self, Exit)`.
    pub trait InnerWalkable: Any {
        type InnerWalker<'a>: TypeWalker;
        fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a>;

        /// Yields `(self, Enter)`, walks over the inner walker, and finishes by yielding `(self,
        /// Exit)`.
        fn walk_this_and_inside<'a>(
            &'a mut self,
        ) -> walk_this_and_inside::ThisAndInsideWalker<'a, Self> {
            use std::marker::PhantomData;
            walk_this_and_inside::ThisAndInsideWalker {
                this: self,
                borrow: PhantomData,
                next_step: walk_this_and_inside::ThisAndInsideWalkerNextStep::Start,
            }
        }
    }

    /// The inner workings of `walk_this_and_inside`.
    pub mod walk_this_and_inside {
        use crate::*;
        use std::any::Any;
        use std::marker::PhantomData;

        use super::InnerWalkable;

        pub struct ThisAndInsideWalker<'a, T: InnerWalkable + ?Sized> {
            /// This is morally a `&'a mut T` but we need a pointer to keep it around while the insides
            /// are borrowed.
            /// SAFETY: don't access while a derived reference is live.
            pub(super) this: *mut T,
            pub(super) borrow: PhantomData<&'a mut T>,
            pub(super) next_step: ThisAndInsideWalkerNextStep<'a, T>,
        }

        pub(super) enum ThisAndInsideWalkerNextStep<'a, T: InnerWalkable + ?Sized> {
            Start,
            EnterInside,
            // The lifetime `'a` here is a lie: we drop the walker before `'a` ends, and invalidate
            // the reference it came from afterwards. However, the borrow-checker ensures this `'a`
            // lifetime canno escape, so it's safe if we're careful enough.
            WalkInside(<T as InnerWalkable>::InnerWalker<'a>),
            Done,
        }

        impl<'a, T: InnerWalkable> LendingIteratorItem for ThisAndInsideWalker<'a, T> {
            type Item<'item> = (&'item mut dyn Any, Event);
        }

        impl<'a, T: InnerWalkable> LendingIterator for ThisAndInsideWalker<'a, T> {
            fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
                // This is pretty much a hand-rolled `Generator`. With nightly rustc we might be able
                // to use `yield` to make this easier to write.
                use Event::*;
                use ThisAndInsideWalkerNextStep::*;
                if let Start = self.next_step {
                    self.next_step = EnterInside;
                    // SAFETY: No references derived from `this` are live because we haven't
                    // created one yet. Moreover `*this` is borrowed for `'a` so we can return a
                    // derived borrow with lifetime smaller than `'a`.
                    let this = unsafe { &mut *self.this };
                    return Some((this as &mut dyn Any, Enter));
                }
                if let EnterInside = self.next_step {
                    // SAFETY: No references derived from `this` are live because the only one we
                    // created was returned and the borrow-checker guarantees `next()` can only be
                    // called again after it is dropped.
                    // We are lying about lifetimes here: the walked is constructed with lifetime
                    // `'a` even though we will invalidate the derived reference before the end of
                    // `'a`. The user can't know thanks to the HRTB, so this is safe if we drop the
                    // walker before we invalidate the reference it was constructed from.
                    let this = unsafe { &mut *self.this };
                    let walker = this.walk_inner();
                    self.next_step = WalkInside(walker);
                    // Continue to next case.
                }
                if let WalkInside(ref mut walker) = self.next_step {
                    if let Some(next) = walker.next() {
                        return Some(next);
                    } else {
                        // This drops the walker.
                        self.next_step = Done;
                        // SAFETY: The HRTB on `F` guarantees that any borrows derived from the
                        // argument we passed to `walk_inner` must have flowed into `W`. Since we
                        // just dropped the walker, there are no live references derived from
                        // `this`. Moreover `*this` is borrowed for `'a` so we can return a derived
                        // borrow with lifetime smaller than `'a`.
                        let this = unsafe { &mut *self.this };
                        return Some((this as &mut dyn Any, Exit));
                    }
                }
                None
            }
        }
    }

    // Visits a single type (without looking deeper into it). Can be used to visit base types.
    pub fn single<'a, T: 'static>(val: &'a mut T) -> single::Single<'a, T> {
        single::Single {
            val,
            next_event: Some(Event::Enter),
        }
    }

    /// The inner workings of `single`.
    pub mod single {
        use crate::*;
        use std::any::Any;

        pub struct Single<'a, T> {
            pub(super) val: &'a mut T,
            pub(super) next_event: Option<Event>,
        }

        impl<'a, T: Any> LendingIteratorItem for Single<'a, T> {
            type Item<'item> = (&'item mut dyn Any, Event);
        }

        impl<'a, T: Any> LendingIterator for Single<'a, T> {
            fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
                use Event::*;
                let e = self.next_event?;
                self.next_event = match e {
                    Enter => Some(Exit),
                    Exit => None,
                };
                Some((self.val, e))
            }
        }
    }

    /// Visit all subobjects of type `U` of `obj`
    pub fn visit<T: Walkable, U: 'static>(obj: &mut T, callback: impl FnMut(&mut U, Event)) {
        obj.walk().inspect_t(callback).run_to_completion();
    }
}

impl Walkable for u8 {
    type Walker<'a> = impl TypeWalker;
    fn walk<'a>(&'a mut self) -> Self::Walker<'a> {
        single(self)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Point {
    x: u8,
    y: u8,
}

// This can be derived automatically.
impl InnerWalkable for Point {
    type InnerWalker<'a> = impl TypeWalker;
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
        self.x.walk().chain(self.y.walk())
    }
}
impl Walkable for Point {
    type Walker<'a> = impl TypeWalker;
    fn walk<'a>(&'a mut self) -> Self::Walker<'a> {
        self.walk_this_and_inside()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum OneOrTwo {
    One(u8),
    Two(Point),
}

// This can be derived automatically.
impl InnerWalkable for OneOrTwo {
    type InnerWalker<'a> = impl TypeWalker;
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
        match self {
            OneOrTwo::One(one) => Either::Left(one.walk()),
            OneOrTwo::Two(two) => Either::Right(two.walk()),
        }
    }
}
impl Walkable for OneOrTwo {
    type Walker<'a> = impl TypeWalker;
    fn walk<'a>(&'a mut self) -> Self::Walker<'a> {
        self.walk_this_and_inside()
    }
}

#[test]
fn test_inspect() {
    use Event::*;
    let mut p = Point { x: 42, y: 12 };
    p.walk()
        .inspect_t(|p: &mut Point, e| match e {
            Enter => {
                assert_eq!(p.x, 42);
                assert_eq!(p.y, 12);
            }
            Exit => {
                assert_eq!(p.x, 44);
                assert_eq!(p.y, 14);
            }
        })
        .inspect_t(|x: &mut u8, _| {
            *x += 1;
        })
        .run_to_completion();

    assert_eq!(p.x, 44);
    assert_eq!(p.y, 14);
}

#[test]
fn test_nested() {
    let mut one_or_two = OneOrTwo::Two(Point { x: 42, y: 12 });

    let mut walker = one_or_two.walk().filter(|(_, e)| matches!(e, Event::Enter));
    let (x, _) = walker.next_t::<u8>().unwrap();
    *x = 101;
    let (y, _) = walker.next_t::<u8>().unwrap();
    *y = 202;
    assert!(walker.next().is_none());
    drop(walker);

    assert_eq!(one_or_two, OneOrTwo::Two(Point { x: 101, y: 202 }));
}

#[test]
fn test_zip() {
    use Event::*;
    let mut p = Point { x: 10, y: 20 };
    let mut q = Point { x: 100, y: 200 };
    let mut iter = p.walk().zip(q.walk());

    let ((_, Enter), (_, Enter)) = iter.next().unwrap() else {
        panic!()
    };

    let ((p_x, Enter), (q_x, Enter)) = iter.next().unwrap() else {
        panic!()
    };
    let p_x = p_x.downcast_mut::<u8>().unwrap();
    let q_x = q_x.downcast_mut::<u8>().unwrap();
    assert_eq!(*p_x, 10);
    assert_eq!(*q_x, 100);
    *p_x += 1;
    *q_x += 1;

    drop(iter);

    assert_eq!(p.x, 11);
    assert_eq!(q.x, 101);
}
