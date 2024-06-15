//! Utilities for visiting multiple values in lockstep.
use crate::{lending_iterator_ext::Inspect, prelude::*, walker::OuterWalker};

pub use zip_walkers::ZipWalkers;

/// A visitor for visiting multiple values of the same type in parallel.
pub trait ZipVisitorMut<const N: usize> {
    fn visit(&mut self, objs: [&mut dyn Any; N], event: Event);
}

/// An dynamically-typed iterator over the subobjects of an array of values.
///
/// This is the equivalent of [`TypeWalker`], modified to work over `N` values in parallel.
#[nougat::apply(nougat::Gat!)]
pub trait ZipWalker<const N: usize>:
    Sized + LendingIterator + for<'item> LendingIterator<Item<'item> = ([&'item mut dyn Any; N], Event)>
{
    /// Returns the next values of type `T`.
    fn next_t<T: 'static>(&mut self) -> Option<([&mut T; N], Event)> {
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

    /// Calls `f` on each visited items of type `T`. Returns a new visitor that visits on the same
    /// items (of course `f` may have modified them in flight).
    fn inspect_t<T: 'static, F: FnMut([&mut T; N], Event)>(
        self,
        mut f: F,
    ) -> Inspect<Self, impl FnMut(&mut ([&mut dyn Any; N], Event))> {
        self.inspect(move |(next, event)| {
            if let Some(next_t) = next.each_mut().try_map(|v| v.downcast_mut::<T>()) {
                f(next_t, *event)
            }
        })
    }

    fn inspect_enter<T: 'static, F: FnMut([&mut T; N])>(
        self,
        mut f: F,
    ) -> Inspect<Self, impl FnMut(&mut ([&mut dyn Any; N], Event))> {
        self.inspect_t(move |objs, e| {
            if matches!(e, Event::Enter) {
                f(objs)
            }
        })
    }

    fn inspect_with<V: ZipVisitorMut<N>>(
        self,
        mut v: V,
    ) -> Inspect<Self, impl FnMut(&mut ([&mut dyn Any; N], Event))> {
        self.inspect(move |(next, event)| v.visit(next.each_mut().map(|x| &mut **x), *event))
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
#[nougat::apply(nougat::Gat!)]
impl<T, const N: usize> ZipWalker<N> for T
where
    T: LendingIterator,
    T: for<'item> LendingIterator<Item<'item> = ([&'item mut dyn Any; N], Event)>,
{
}

/// Zips a number of identical walkers.
///
/// Assuming they output the same types and events in the same order, this can be used to iterate
/// over multiple values in lockstep. The output is a [`ZipWalker`].
pub fn zip_walkers<I: TypeWalker, const N: usize>(walkers: [I; N]) -> ZipWalkers<I, N> {
    ZipWalkers { walkers }
}

/// Zips a number of identical walkables.
///
/// See [`zip_walkers()`] for details.
pub fn zip_walkables<T: Walkable, const N: usize>(
    walkables: [&mut T; N],
) -> ZipWalkers<OuterWalker<'_, T>, N> {
    zip_walkers(walkables.map(|x| x.walk()))
}

/// The inner workings of `zip_walkers`.
mod zip_walkers {
    use super::*;

    /// The output of [`zip_walkers()`] and [`zip_walkables()`].
    pub struct ZipWalkers<I, const N: usize> {
        pub(super) walkers: [I; N],
    }

    #[nougat::gat]
    impl<I: TypeWalker, const N: usize> LendingIterator for ZipWalkers<I, N> {
        type Item<'item> = ([&'item mut dyn Any; N], Event);
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
