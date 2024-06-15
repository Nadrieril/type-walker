use crate::lending_iterator::inspect::Inspect;
use crate::*;
use higher_kinded_types::ForLt;
use std::any::Any;
use zip_walkers::ZipWalkers;

/// A type that can be visited.
pub trait Walkable {
    type Walker<'a>: TypeWalker
    where
        Self: 'a;
    fn walk<'a>(&'a mut self) -> Self::Walker<'a>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    Enter,
    Exit,
}

/// A type visitor.
/// This is a trait alias for the right kind of lending iterator, with extra provided methods
/// for convenience.
pub trait TypeWalker:
    Sized + LendingIterator + for<'item> LendingIteratorItem<'item, Item = (&'item mut dyn Any, Event)>
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

    fn inspect_with<V: TypeVisitor>(
        self,
        mut v: V,
    ) -> Inspect<Self, impl FnMut(&mut (&mut dyn Any, Event))> {
        self.inspect(move |(next, event): &mut (&mut dyn Any, Event)| v.visit(*next, *event))
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
            outer: self,
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
        pub(super) outer: *mut T,
        pub(super) borrow: PhantomData<&'a mut T>,
        pub(super) next_step: ThisAndInsideWalkerNextStep<'a, T>,
    }

    pub(super) enum ThisAndInsideWalkerNextStep<'a, T: InnerWalkable + ?Sized> {
        Start,
        EnterInside,
        // The lifetime `'a` here is a lie: we drop the walker before `'a` ends, and invalidate
        // the reference it came from afterwards. However, the borrow-checker ensures this `'a`
        // lifetime cannot escape, so it's safe if we're careful enough.
        WalkInside(<T as InnerWalkable>::InnerWalker<'a>),
        Done,
    }

    impl<'a, 'item, T: InnerWalkable> LendingIteratorItem<'item> for ThisAndInsideWalker<'a, T> {
        type Item = (&'item mut dyn Any, Event);
    }

    impl<'a, T: InnerWalkable> LendingIterator for ThisAndInsideWalker<'a, T> {
        fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
            use polonius_the_crab::*;
            // This is pretty much a hand-rolled `Generator`. With nightly rustc we might be able
            // to use `yield` to make this easier to write.
            use Event::*;
            use ThisAndInsideWalkerNextStep::*;
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

pub fn empty_walker() -> Empty<ForLt!((&'_ mut dyn Any, Event))> {
    empty()
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

/// Zips a number of identical walkers. Assuming they output the same types and events in the
/// same order, this can be used to iterate over multiple values in lockstep. The output is not
/// a `TypeWalker` because the types don't match, however it has appropriate convenience
/// methods to consume it.
pub fn zip_walkers<I: TypeWalker, const N: usize>(walkers: [I; N]) -> ZipWalkers<I, N> {
    ZipWalkers { walkers }
}

pub fn zip_walkables<T: Walkable, const N: usize>(
    walkables: [&mut T; N],
) -> ZipWalkers<T::Walker<'_>, N> {
    zip_walkers(walkables.map(|x| x.walk()))
}

/// The inner workings of `zip_walkers`.
pub mod zip_walkers {
    use crate::*;
    use std::any::Any;

    pub struct ZipWalkers<I, const N: usize> {
        pub(super) walkers: [I; N],
    }

    impl<I: TypeWalker, const N: usize> ZipWalkers<I, N> {
        /// Returns the next value of type `T`.
        pub fn next_t<T: 'static>(&mut self) -> Option<([&mut T; N], Event)> {
            use polonius_the_crab::*;
            let mut this = self;
            polonius_loop!(|this| -> Option<([&'polonius mut T; N], Event)> {
                let (next, e) = polonius_try!(this.next());
                let ts: Option<[&mut T; N]> = next.try_map(|v| v.downcast_mut::<T>());
                if let Some(ts) = ts {
                    polonius_return!(Some((ts, e)));
                }
            })
        }
    }

    impl<'item, I: TypeWalker, const N: usize> LendingIteratorItem<'item> for ZipWalkers<I, N> {
        type Item = ([&'item mut dyn Any; N], Event);
    }

    impl<I: TypeWalker, const N: usize> LendingIterator for ZipWalkers<I, N> {
        fn next(&mut self) -> Option<Item<'_, Self>> {
            let nexts = self.walkers.each_mut().try_map(|walker| walker.next())?;
            let events: [Event; N] = nexts.each_ref().map(|(_, e)| *e);
            let event = events[0];
            if events.iter().any(|e| *e != event) {
                return None;
            }
            let nexts: [&mut dyn Any; N] = nexts.map(|(x, _)| x);
            Some((nexts, event))
        }
    }
}

/// Visit all subobjects of type `U` of `obj`
pub fn visit<T: Walkable, U: 'static>(obj: &mut T, callback: impl FnMut(&mut U, Event)) {
    obj.walk().inspect_t(callback).run_to_completion();
}

pub fn visit_enter<T: Walkable, U: 'static>(obj: &mut T, callback: impl FnMut(&mut U)) {
    obj.walk().inspect_enter(callback).run_to_completion();
}

/// Implementations on std types.
mod std_impls {
    use crate::Walkable;

    impl<T: Walkable> Walkable for Box<T> {
        // Box the walker otherwise recursive structures will have infinite-size walkers.
        type Walker<'a> = Box<T::Walker<'a>> where T: 'a;
        fn walk<'a>(&'a mut self) -> Self::Walker<'a> {
            Box::new((**self).walk())
        }
    }
}
