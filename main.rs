#![feature(impl_trait_in_assoc_type)]

use lending_iterator::*;
use visitor_crate::*;

/// The lending iterator trait and helpers.
pub mod lending_iterator {
    //! GAT hack taken from https://docs.rs/lending-iterator/latest/lending_iterator. With a real
    //! GAT we can't write the `TypeWalker` trait alias because the `for<'a>` constraint becomes
    //! impossible to satisfy. Idk if this is a trait solver bug or a type system limitation.
    pub trait LendingIterator: Sized
    where
        Self: for<'item> LendingIteratorItem<'item>,
    {
        fn next(&mut self) -> Option<Item<'_, Self>>;

        /// Provided method that calls `f` on each item.
        fn inspect<F: for<'a> FnMut(&mut Item<'a, Self>)>(self, f: F) -> inspect::Inspect<Self, F> {
            inspect::Inspect { iter: self, f }
        }

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

    pub trait LendingIteratorItem<'item, Bounds = &'item Self> {
        type Item;
    }

    pub type Item<'lt, I> = <I as LendingIteratorItem<'lt>>::Item;

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
}

/// The visitor crate would provide these definitions.
pub mod visitor_crate {
    use crate::lending_iterator::inspect::Inspect;
    use crate::*;
    use std::any::Any;

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

    /// This is a trait alias with extra provided methods.
    pub trait TypeWalker:
        Sized
        + LendingIterator
        + for<'item> LendingIteratorItem<'item, Item = (&'item mut dyn Any, Event)>
    {
        /// Provided method that calls `f` on each visited item of type `T`. Returns a new iterator
        /// that iterates on the same items (of course `f` may have modified them in flight).
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

        /// Runs to completion.
        fn run(&mut self) {
            loop {
                let next = self.next();
                if next.is_none() {
                    break;
                }
            }
        }
    }
    impl<T> TypeWalker for T
    where
        T: LendingIterator,
        T: for<'item> LendingIteratorItem<'item, Item = (&'item mut dyn Any, Event)>,
    {
    }

    /// A walker that enters `this`, walks over the walker returned by `walk_inside`, and exits
    /// `this`.
    pub fn walk_this_and_inside<'a, T, F, W>(
        this: &'a mut T,
        walk_inside: F,
    ) -> walk_this_and_inside::ThisAndInsideWalker<'a, T, F, W>
    where
        F: FnOnce(&'a mut T) -> W,
        W: TypeWalker,
    {
        use std::marker::PhantomData;
        walk_this_and_inside::ThisAndInsideWalker {
            this,
            borrow: PhantomData,
            walk_inside: Some(walk_inside),
            next_step: walk_this_and_inside::ThisAndInsideWalkerNextStep::Start,
        }
    }

    pub mod walk_this_and_inside {
        use crate::*;
        use std::any::Any;
        use std::marker::PhantomData;

        pub struct ThisAndInsideWalker<'a, T, F, W> {
            /// This is morally a `&'a mut T` but we need a pointer to keep it around while the insides
            /// are borrowed.
            /// SAFETY: don't access while a derived reference is live.
            pub(super) this: *mut T,
            pub(super) borrow: PhantomData<&'a mut T>,
            pub(super) walk_inside: Option<F>,
            pub(super) next_step: ThisAndInsideWalkerNextStep<W>,
        }

        pub(super) enum ThisAndInsideWalkerNextStep<W> {
            Start,
            EnterInside,
            WalkInside(W),
            Done,
        }

        impl<'a, 'item, T, F, W> LendingIteratorItem<'item> for ThisAndInsideWalker<'a, T, F, W> {
            type Item = (&'item mut dyn Any, Event);
        }

        impl<'a, T, F, W> LendingIterator for ThisAndInsideWalker<'a, T, F, W>
        where
            T: Any,
            F: FnOnce(&'a mut T) -> W,
            W: TypeWalker,
        {
            fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
                // This is pretty much a hand-rolled `Generator`. With nightly rustc we might be able
                // to use `yield` to make this easier to write.
                use Event::*;
                use ThisAndInsideWalkerNextStep::*;
                if let Start = self.next_step {
                    self.next_step = EnterInside;
                    // SAFETY: no references derived from `this` are live, and `this` is borrowed
                    // for `'a`.
                    let this = unsafe { &mut *self.this };
                    return Some((this as &mut dyn Any, Enter));
                }
                if let EnterInside = self.next_step {
                    // SAFETY: no references derived from `this` are live, and `this` is borrowed
                    // for `'a`.
                    let this = unsafe { &mut *self.this };
                    let walker = (self.walk_inside.take().unwrap())(this);
                    self.next_step = WalkInside(walker);
                    // Continue to next case.
                }
                if let WalkInside(ref mut walker) = self.next_step {
                    if let Some(next) = walker.next() {
                        return Some(next);
                    } else {
                        self.next_step = Done;
                        // SAFETY: no references derived from `this` are live, and `this` is borrowed
                        // for `'a`.
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
        obj.walk().inspect_t(callback).run();
    }
}

#[derive(Debug)]
pub struct Point {
    x: u8,
    y: u8,
}

// This can be derived automatically.
impl Walkable for Point {
    type Walker<'a> = impl TypeWalker;
    fn walk<'a>(&'a mut self) -> Self::Walker<'a> {
        walk_this_and_inside(self, |this| single(&mut this.x).chain(single(&mut this.y)))
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
        .run();
    println!("Final state of the Point: {p:?}");
}
