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
    // Utility struct that encapsulates the `unsafe`.
    mod ref_and_derived {
        use higher_kinded_types::ForLifetime;
        use std::marker::PhantomData;

        /// Keeps a `&'a mut T` alongside a value that captures a derived borrow to it. Provides a safe
        /// API for that.
        pub struct RefAndDerived<'a, T: ?Sized, Derived: ForLifetime> {
            /// This is morally a `&'a mut T` but we need a pointer to keep it around while the insides
            /// are borrowed.
            /// SAFETY: don't access while a derived reference is live.
            outer: *mut T,
            borrow: PhantomData<&'a mut T>,
            // The lifetime `'a` here is a lie: we drop the derived value before `'a` ends, and
            // invalidate the reference it came from afterwards. However, the borrow-checker ensures
            // this `'a` lifetime cannot escape, so (I hope) it's safe if we're careful enough.
            derived: <Derived as ForLifetime>::Of<'a>,
        }

        impl<'a, T: ?Sized, Derived: ForLifetime> RefAndDerived<'a, T, Derived> {
            // The HRTB in `derive` is the key to the safety of the API.
            pub fn new(
                outer: &'a mut T,
                derive: impl for<'b> FnOnce(&'b mut T) -> <Derived as ForLifetime>::Of<'b>,
            ) -> Self {
                // Convert to a raw pointer.
                let outer: *mut T = outer;
                // SAFETY: By the signature of this function, `outer` is valid for `'a`. Moreover
                // we won't access `outer` until `derived` is dropped.
                let inner: &'a mut T = unsafe { &mut *outer };
                let derived = derive(inner);
                RefAndDerived {
                    outer,
                    borrow: PhantomData,
                    derived,
                }
            }

            pub fn derived<'b>(&'b mut self) -> &'b mut <Derived as ForLifetime>::Of<'b>
            where
                'a: 'b,
            {
                let derived = &mut self.derived;
                // SAFETY: Since `derive` could have been called with any `'b` shorter than `'a`,
                // it is ok to pretend it was. The HRTB of `derive` ensures this lie cannot be
                // observed.
                // This is probably a bad idea with contravariant lifetimes anyway.
                unsafe { std::mem::transmute(derived) }
            }

            pub fn take(self) -> &'a mut T {
                let RefAndDerived {
                    outer,
                    borrow: _,
                    derived,
                } = self;
                drop(derived);
                // SAFETY: All derived references have been dropped. Moreover, `outer` is valid for
                // `&'a`, and the signature of this function ensure we convert to a borrow with
                // lifetime `'a`.
                unsafe { &mut *outer }
            }
        }
    }

    use super::*;
    use std::any::Any;

    use super::Walkable;
    use ref_and_derived::RefAndDerived;

    /// Handles the yielding of `(self, Enter)` and `(self, Exit)` before/after `T`'s inner walker.
    pub struct OuterWalker<'a, T: Walkable + ?Sized> {
        next_step: OuterWalkerNextStep<'a, T>,
    }

    impl<'a, T: Walkable + ?Sized> OuterWalker<'a, T> {
        pub fn new(outer: &'a mut T) -> OuterWalker<'a, T> {
            OuterWalker {
                next_step: OuterWalkerNextStep::Start(outer),
            }
        }
    }

    pub(super) enum OuterWalkerNextStep<'a, T: Walkable + ?Sized> {
        Start(&'a mut T),
        EnterInside(RefAndDerived<'a, T, ForLt!(&'_ mut T)>),
        // The lifetime `'a` here is a lie: we drop the walker before `'a` ends, and invalidate
        // the reference it came from afterwards. However, the borrow-checker ensures this `'a`
        // lifetime cannot escape, so it's safe if we're careful enough.
        WalkInside(RefAndDerived<'a, T, ForLt!(<T as Walkable>::InnerWalker<'_>)>),
        Done,
    }

    #[nougat::gat]
    impl<'a, T: Walkable> LendingIterator for OuterWalker<'a, T> {
        type Item<'item> = (&'item mut dyn Any, Event);
        fn next<'b>(&'b mut self) -> Option<(&'b mut dyn Any, Event)> {
            use polonius_the_crab::*;
            // This is pretty much a hand-rolled `Generator`. With nightly rustc we might be able
            // to use `yield` to make this easier to write.
            use Event::*;
            use OuterWalkerNextStep::*;
            let mut this = self;
            polonius!(|this| -> Option<(&'polonius mut dyn Any, Event)> {
                if let Start(_) = &this.next_step {
                    let Start(outer) = std::mem::replace(&mut this.next_step, Done) else {
                        panic!()
                    };
                    this.next_step = EnterInside(RefAndDerived::new(outer, |outer| outer));
                    let EnterInside(ref mut outer) = this.next_step else {
                        panic!()
                    };
                    let outer: &mut T = *outer.derived();
                    polonius_return!(Some((outer as &mut dyn Any, Enter)));
                }
            });
            if let EnterInside(_) = &this.next_step {
                let EnterInside(outer) = std::mem::replace(&mut this.next_step, Done) else {
                    panic!()
                };
                let outer = outer.take();
                this.next_step = WalkInside(RefAndDerived::new(outer, |outer| outer.walk_inner()));
                // Continue to next case.
            }
            polonius!(|this| -> Option<(&'polonius mut dyn Any, Event)> {
                if let WalkInside(ref mut ref_and_walker) = this.next_step {
                    if let Some(next) = ref_and_walker.derived().next() {
                        polonius_return!(Some(next));
                    }
                }
            });
            if let WalkInside(ref_and_walker) = std::mem::replace(&mut this.next_step, Done) {
                let outer = ref_and_walker.take();
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
