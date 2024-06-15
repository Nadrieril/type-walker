#![feature(impl_trait_in_assoc_type)]
use lending_iterator::*;
use visitor::*;

/// The lending iterator trait and helpers.
// I define my own instead of using https://docs.rs/lending-iterator/latest/lending_iterator
// because that one doesn't have `inspect` and `chain`.
pub mod lending_iterator {
    pub use chain::Chain;
    pub use filter::Filter;
    pub use inspect::Inspect;

    // GAT hack taken from https://docs.rs/lending-iterator/latest/lending_iterator. With a real
    // GAT we can't write the `TypeWalker` trait alias because the `Self: 'a` bound makes the
    // `for<'a>` constraint impossible to satisfy. Idk if this is a trait solver bug or a type
    // system limitation.
    pub trait LendingIterator: Sized
    where
        Self: for<'item> LendingIteratorItem<'item>,
    {
        fn next(&mut self) -> Option<Item<'_, Self>>;

        /// Like `Iterator::inspect`.
        fn inspect<F: for<'a> FnMut(&mut Item<'a, Self>)>(self, f: F) -> inspect::Inspect<Self, F> {
            inspect::Inspect { iter: self, f }
        }

        /// Like `Iterator::filter`.
        fn filter<F: for<'a> FnMut(&Item<'a, Self>) -> bool>(
            self,
            f: F,
        ) -> filter::Filter<Self, F> {
            filter::Filter { iter: self, f }
        }

        /// Like `Iterator::chain`.
        fn chain<J: LendingIterator>(self, other: J) -> chain::Chain<Self, J>
        where
            J: for<'item> LendingIteratorItem<'item, Item = Item<'item, Self>>,
        {
            chain::Chain {
                first: Some(self),
                second: Some(other),
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
        + for<'item> LendingIteratorItem<'item, Item = (&'item mut dyn Any, Event)>
    {
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

        /// Returns the next value of type `T`.
        fn next_t<T: 'static>(&mut self) -> Option<(&mut T, Event)> {
            while let Some((next, e)) = self.next() {
                if let Some(next) = next.downcast_mut::<T>() {
                    return Some((next, e));
                }
            }
            None
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
        T: for<'item> LendingIteratorItem<'item, Item = (&'item mut dyn Any, Event)>,
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

        impl<'a, 'item, T: InnerWalkable> LendingIteratorItem<'item> for ThisAndInsideWalker<'a, T> {
            type Item = (&'item mut dyn Any, Event);
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

        impl<'a, 'item, T: Any> LendingIteratorItem<'item> for Single<'a, T> {
            type Item = (&'item mut dyn Any, Event);
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

#[derive(Debug)]
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

#[derive(Debug)]
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

fn main() {
    let mut p = Point { x: 42, y: 12 };
    p.walk()
        .inspect_t(|p: &mut Point, e| {
            println!("We got a Point({e:?}): {p:?}");
        })
        .inspect_t(|x: &mut u8, e| {
            println!("Zeroing some u8({e:?}): {x}");
            *x = 0;
        })
        .run_to_completion();

    // Now the point is all 0s. We set some nice values instead, going through `OneOrTwo` for
    // demonstration purposes.
    let mut one_or_two = OneOrTwo::Two(p);
    let mut walker = one_or_two.walk().filter(|(_, e)| matches!(e, Event::Enter));
    let (x, _) = walker.next_t::<u8>().unwrap();
    *x = 101;
    let (y, _) = walker.next_t::<u8>().unwrap();
    *y = 202;
    assert!(walker.next().is_none());
    drop(walker);

    println!("Final state of the value: {one_or_two:?}");
}
