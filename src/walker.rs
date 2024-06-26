//! Traits and utilities for iterating over the contents of a value.
//!
//! The main trait of this crate is [`Walkable`], which describes a type that can be recursively
//! walked. Calling `x.walk()` gives an iterator that yields the sub-objects of `x` in a
//! dynamically-typed fashion. The methods provided by this module can be used to specialize this
//! exploration to types of interest.
use crate::lending_iterator_ext::*;
use derive_visitor::{DriveMut, Event, VisitorMut};
use higher_kinded_types::ForLt;
use lending_iterator::{lending_iterator::adapters::Filter, prelude::*};
pub use outer_walker::OuterWalker;
use std::any::Any;
pub use walk_driver::WalkDriver;

/// A type that can be walked.
///
/// This is similar to [`IntoIterator`], but here `Walker` may borrow from `self`, and is a
/// [`TypeWalker`] instead of an arbitrary iterator.
///
/// When walking over a value, we yield twice for each subobject: the first time we encounter the
/// object we yield `(&mut object, Event::Enter)`; after that we walk subobjects of `object`; once
/// we're done we yield `(&mut object, Event::Exit)`.
///
/// To implement this trait, implement [`Walkable::walk_inner()`].
pub trait Walkable: Any + Sized {
    /// Walk over this value and its subobjects.
    ///
    /// This method is provided and should not be overriden. Implement [`Walkable::walk_inner()`] instead.
    fn walk<'a>(&'a mut self) -> OuterWalker<'a, Self> {
        OuterWalker::new(self)
    }

    /// Walker over the subobjects.
    type InnerWalker<'a>: TypeWalker
    where
        Self: 'a;

    /// Walk over the subobjects of `self`.
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a>;

    /// Drive a visitor through this value.
    fn drive_mut<V: VisitorMut>(&mut self, visitor: &mut V) {
        self.walk().inspect_with(visitor).run_to_completion()
    }

    /// Wraps this into a [`derive_visitor::DriveMut`] type.
    fn into_driver_mut(self) -> WalkDriver<Self> {
        WalkDriver(self)
    }
}

/// An dynamically-typed iterator over the subobjects of a value.
///
/// This is a trait alias for a lending iterator that yields `(&mut dyn Any, Event)`. It provides
/// convenience methods for dealing with downcasting the yielded objects.
#[nougat::apply(nougat::Gat!)]
pub trait TypeWalker:
    Sized + LendingIterator + for<'item> LendingIterator<Item<'item> = (&'item mut dyn Any, Event)>
{
    /// Returns the next value of type `T`.
    fn next_t<T: 'static>(&mut self) -> Option<(&mut T, Event)> {
        use polonius_the_crab::*;
        let mut this = self;
        polonius_loop!(|this| -> Option<(&'polonius mut T, Event)> {
            let (next, e) = polonius_try!(this.next());
            if let Some(next) = next.downcast_mut::<T>() {
                polonius_return!(Some((next, e)));
            }
        })
    }

    /// Keeps only the [`Event::Enter`] events.
    fn only_enter(self) -> Filter<Self, impl FnMut(&(&mut dyn Any, Event)) -> bool> {
        self.filter(move |(_, event)| matches!(event, Event::Enter))
    }

    /// Calls `f` on each visited item of type `T`. Returns a new visitor that visits on the same
    /// items (of course `f` may have modified them in flight).
    fn inspect_t<T: 'static, F: FnMut(&mut T, Event)>(
        self,
        mut f: F,
    ) -> Inspect<Self, impl FnMut(&mut (&mut dyn Any, Event))> {
        self.inspect(move |(next, event)| {
            if let Some(next_t) = (*next).downcast_mut::<T>() {
                f(next_t, *event)
            }
        })
    }

    fn inspect_enter<T: 'static, F: FnMut(&mut T)>(
        self,
        mut f: F,
    ) -> Inspect<Self, impl FnMut(&mut (&mut dyn Any, Event))> {
        self.inspect_t(move |obj, e| {
            if matches!(e, Event::Enter) {
                f(obj)
            }
        })
    }

    fn inspect_with<V: VisitorMut>(
        self,
        mut v: V,
    ) -> Inspect<Self, impl FnMut(&mut (&mut dyn Any, Event))> {
        self.inspect(move |(next, event)| v.visit(*next, *event))
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
// This is the reason we can't use a clean GAT-based lending iterator: when we do, this
// `for<'item>` bound forces `Self: 'static` which prevents our usecase.
#[nougat::apply(nougat::Gat!)]
impl<T> TypeWalker for T
where
    T: LendingIterator,
    T: for<'item> LendingIterator<Item<'item> = (&'item mut dyn Any, Event)>,
{
}

/// The inner workings of walking `self`.
mod outer_walker {
    use super::*;
    use std::any::Any;
    use std::marker::PhantomData;

    use super::Walkable;

    /// Handles the yielding of `(self, Enter)` and `(self, Exit)` before/after `T`'s inner walker.
    pub struct OuterWalker<'a, T: Walkable + ?Sized> {
        /// This is morally a `&'a mut T` but we need a pointer to keep it around while the insides
        /// are borrowed.
        /// SAFETY: don't access while a derived reference is live.
        outer: *mut T,
        borrow: PhantomData<&'a mut T>,
        next_step: OuterWalkerNextStep<'a, T>,
    }

    impl<'a, T: Walkable + ?Sized> OuterWalker<'a, T> {
        pub fn new(outer: &'a mut T) -> OuterWalker<'a, T> {
            use std::marker::PhantomData;
            OuterWalker {
                outer,
                borrow: PhantomData,
                next_step: OuterWalkerNextStep::Start,
            }
        }
    }

    pub(super) enum OuterWalkerNextStep<'a, T: Walkable + ?Sized> {
        Start,
        EnterInside,
        // The lifetime `'a` here is a lie: we drop the walker before `'a` ends, and invalidate
        // the reference it came from afterwards. However, the borrow-checker ensures this `'a`
        // lifetime cannot escape, so it's safe if we're careful enough.
        WalkInside(<T as Walkable>::InnerWalker<'a>),
        Done,
    }

    #[nougat::gat]
    impl<'a, T: Walkable> LendingIterator for OuterWalker<'a, T> {
        type Item<'item> = (&'item mut dyn Any, Event);
        fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
            use polonius_the_crab::*;
            // This is pretty much a hand-rolled `Generator`. With nightly rustc we might be able
            // to use `yield` to make this easier to write.
            use Event::*;
            use OuterWalkerNextStep::*;
            let mut this = self;
            polonius!(|this| -> Option<(&'polonius mut dyn Any, Event)> {
                if let Start = this.next_step {
                    this.next_step = EnterInside;
                    // SAFETY: No references derived from `this` are live because we haven't
                    // created one yet. Moreover `*this` is borrowed for `'a` so we can return a
                    // derived borrow with lifetime smaller than `'a`.
                    let outer = unsafe { &mut *this.outer };
                    polonius_return!(Some((outer as &mut dyn Any, Enter)));
                }
            });
            if let EnterInside = this.next_step {
                // SAFETY: No references derived from `this` are live because the only one we
                // created was returned and the borrow-checker guarantees `next()` can only be
                // called again after it is dropped.
                // We are lying about lifetimes here: the walked is constructed with lifetime
                // `'a` even though we will invalidate the derived reference before the end of
                // `'a`. The user can't know thanks to the HRTB, so this is safe if we drop the
                // walker before we invalidate the reference it was constructed from.
                let outer = unsafe { &mut *this.outer };
                let walker = outer.walk_inner();
                this.next_step = WalkInside(walker);
                // Continue to next case.
            }
            polonius!(|this| -> Option<(&'polonius mut dyn Any, Event)> {
                if let WalkInside(ref mut walker) = this.next_step {
                    if let Some(next) = walker.next() {
                        polonius_return!(Some(next));
                    }
                }
            });
            if !matches!(this.next_step, Done) {
                // This drops the walker.
                this.next_step = Done;
                // SAFETY: The HRTB on `F` guarantees that any borrows derived from the
                // argument we passed to `walk_inner` must have flowed into `W`. Since we
                // just dropped the walker, there are no live references derived from
                // `this`. Moreover `*this` is borrowed for `'a` so we can return a derived
                // borrow with lifetime smaller than `'a`.
                let outer = unsafe { &mut *this.outer };
                return Some((outer as &mut dyn Any, Exit));
            }
            None
        }
    }
}

mod walk_driver {
    use super::*;

    /// Wraps a [`Walkable`] type into a [`derive_visitor::DriveMut`] type.
    pub struct WalkDriver<T>(pub(super) T);

    impl<T: Walkable> DriveMut for WalkDriver<T> {
        fn drive_mut<V: VisitorMut>(&mut self, visitor: &mut V) {
            self.0.drive_mut(visitor)
        }
    }
}

/// A walker over no objects.
pub fn empty_walker() -> Empty<ForLt!((&'_ mut dyn Any, Event))> {
    empty()
}

/// A walker over a single object (with no subobjects).
pub fn single<'a, T: 'static>(val: &'a mut T) -> single::Single<'a, T> {
    single::Single {
        val,
        next_event: Some(Event::Enter),
    }
}

/// The inner workings of `single`.
mod single {
    use super::*;
    use std::any::Any;

    pub struct Single<'a, T> {
        pub(super) val: &'a mut T,
        pub(super) next_event: Option<Event>,
    }

    #[nougat::gat]
    impl<'a, T: Any> LendingIterator for Single<'a, T> {
        type Item<'item> = (&'item mut dyn Any, Event);
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

/// Visit all subobjects of type `U` of `obj`.
pub fn visit<T: Walkable, U: 'static>(obj: &mut T, callback: impl FnMut(&mut U, Event)) {
    obj.walk().inspect_t(callback).run_to_completion();
}

/// Visit all subobjects of type `U` of `obj`, and only on `Enter`.
pub fn visit_enter<T: Walkable, U: 'static>(obj: &mut T, callback: impl FnMut(&mut U)) {
    obj.walk().inspect_enter(callback).run_to_completion();
}

/// Implementations on std types.
mod std_impls {
    use super::{OuterWalker, Walkable};

    impl<T: Walkable> Walkable for Box<T> {
        // Box the walker otherwise recursive structures will have infinite-size walkers.
        type InnerWalker<'a> = Box<OuterWalker<'a, T>> where T: 'a;
        fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
            Box::new((**self).walk())
        }
    }
}
