#![feature(impl_trait_in_assoc_type)]
#![feature(gen_blocks)]
use std::{any::Any, marker::PhantomData};

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
        fn inspect<F: for<'a> FnMut(&mut Item<'a, Self>)>(self, f: F) -> Inspect<Self, F> {
            Inspect { iter: self, f }
        }

        fn chain<J: LendingIterator>(self, other: J) -> Chain<Self, J>
        where
            J: for<'item> LendingIteratorItem<'item, Item = Item<'item, Self>>,
        {
            Chain {
                first: Some(self),
                second: Some(other),
            }
        }
    }
    pub trait LendingIteratorItem<'item, Bounds = &'item Self> {
        type Item;
    }
    pub type Item<'lt, I> = <I as LendingIteratorItem<'lt>>::Item;

    pub struct Inspect<I, F> {
        iter: I,
        f: F,
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

    pub struct Chain<I, J> {
        first: Option<I>,
        second: Option<J>,
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

/// The visitor crate would provide these definitions.
pub mod visitor_crate {
    use std::any::Any;

    use crate::*;

    #[derive(Debug, Clone, Copy)]
    pub enum Event {
        Enter,
        Exit,
    }

    pub trait Walkable {
        type Walker<'a>: TypeWalker
        where
            Self: 'a;
        fn walk<'a>(&'a mut self) -> Self::Walker<'a>;
    }

    /// This is just a trait alias with extra provided methods.
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

    // Visits a single type (without looking deeper into it). Can be used to visit base types.
    pub fn single<'a, T: 'static>(val: &'a mut T) -> Single<'a, T> {
        Single {
            val,
            next_event: Some(Event::Enter),
        }
    }

    pub struct Single<'a, T> {
        val: &'a mut T,
        next_event: Option<Event>,
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

    /// Visit all subobjects of type `U` of `obj`
    pub fn visit<T: Walkable, U: 'static>(obj: &mut T, callback: impl FnMut(&mut U, Event)) {
        obj.walk().inspect_t(callback).run();
    }
}

impl Walkable for u8 {
    type Walker<'a> = Single<'a, u8>;
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
impl Walkable for Point {
    type Walker<'a> = PointIter<'a>;
    fn walk<'a>(&'a mut self) -> Self::Walker<'a> {
        PointIter {
            this: self,
            borrow: PhantomData,
            next_step: PointNextStep::Start,
        }
    }
}
enum PointNextStep<'a> {
    Start,
    EnterFields,
    WalkFields(Chain<<u8 as Walkable>::Walker<'a>, <u8 as Walkable>::Walker<'a>>),
    Done,
}
pub struct PointIter<'a> {
    /// This is morally a `&'a mut Point` but we need a pointer to keep it around while the insides
    /// are borrowed.
    /// SAFETY: don't access while a derived reference is live.
    this: *mut Point,
    borrow: PhantomData<&'a mut Point>,
    next_step: PointNextStep<'a>,
}
impl<'a, 'item> LendingIteratorItem<'item> for PointIter<'a> {
    type Item = (&'item mut dyn Any, Event);
}
impl<'a> LendingIterator for PointIter<'a> {
    fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
        // This is in fact a hand-rolled `Generator`. With nightly rustc we might be able
        // to use `yield` to make this even easier to write.
        use Event::*;
        use PointNextStep::*;
        if let Start = self.next_step {
            self.next_step = EnterFields;
            // SAFETY: no references derived from `this` are live, and `this` is borrowed
            // for `'a`.
            let this = unsafe { &mut *self.this };
            return Some((this as &mut dyn Any, Enter));
        }
        if let EnterFields = self.next_step {
            // SAFETY: no references derived from `this` are live, and `this` is borrowed
            // for `'a`.
            let this = unsafe { &mut *self.this };
            self.next_step = WalkFields(this.x.walk().chain(this.y.walk()));
            // Continue to next case.
        }
        if let WalkFields(ref mut walker) = self.next_step {
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
