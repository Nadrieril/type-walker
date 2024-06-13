#![feature(impl_trait_in_assoc_type)]
#![feature(gen_blocks)]
use std::any::Any;

use lending_iterator::*;
use visitor_crate::*;

/// The lending iterator trait and helpers.
pub mod lending_iterator {
    pub trait LendingIterator: Sized {
        type Item<'a>
        where
            Self: 'a;

        fn next(&mut self) -> Option<Self::Item<'_>>;

        /// Provided method that calls `f` on each item.
        fn inspect<F: for<'a> FnMut(&mut Self::Item<'a>)>(self, f: F) -> Inspect<Self, F> {
            Inspect { iter: self, f }
        }
    }

    pub struct Inspect<I, F> {
        iter: I,
        f: F,
    }

    impl<I, F> LendingIterator for Inspect<I, F>
    where
        I: LendingIterator,
        F: for<'a> FnMut(&mut I::Item<'a>),
    {
        type Item<'a> = I::Item<'a> where I: 'a, F: 'a;

        fn next(&mut self) -> Option<Self::Item<'_>> {
            let mut next = self.iter.next();
            if let Some(next) = next.as_mut() {
                (self.f)(next)
            }
            next
        }
    }
}

/// The visitor crate would provide these definitions.
pub mod visitor_crate {
    use std::{any::Any, marker::PhantomData};

    use crate::LendingIterator;

    #[derive(Debug, Clone, Copy)]
    pub enum Event {
        Enter,
        Exit,
    }

    pub trait Visitable {
        // type Iter<'a>: for<'b> LendingIterator<Item<'b> = (&'b mut dyn Any, Event)>
        type Iter<'a>: VisitIter
        where
            Self: 'a;
        fn visit_iter<'a>(&'a mut self) -> Self::Iter<'a>;
    }

    /// An iterator-like state machine that returns the next field to visit on each call to `next`.
    /// Just like `Iterator`, it has convenient provided methods. Implementors should only
    /// implement `field`.
    pub trait VisitIter: Sized {
        fn next(&mut self) -> Option<(&mut dyn Any, Event)>;

        /// Provided method that calls `f` on each visited item of type `T`. Returns a new iterator
        /// that iterates on the same items (of course `f` may have modified them in flight).
        fn inspect_t<T: 'static, F: FnMut(&mut T, Event)>(self, f: F) -> Inspect<Self, T, F> {
            Inspect {
                iter: self,
                f,
                marker: PhantomData,
            }
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

    // impl<T> VisitIter for T
    // where
    //     T: for<'a> LendingIterator<Item<'a> = (&'a mut dyn Any, Event)>
    // {
    //     fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
    //         <Self as LendingIterator>::next(self)
    //     }
    // }

    pub struct Inspect<I, T, F> {
        iter: I,
        f: F,
        marker: PhantomData<T>,
    }

    impl<I, T, F> VisitIter for Inspect<I, T, F>
    where
        I: VisitIter,
        F: FnMut(&mut T, Event),
        T: 'static,
    {
        fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
            <Self as LendingIterator>::next(self)
        }
    }

    impl<I, T, F> LendingIterator for Inspect<I, T, F>
    where
        I: VisitIter,
        F: FnMut(&mut T, Event),
        T: 'static,
    {
        type Item<'b> = (&'b mut dyn Any, Event) where Self: 'b;
        fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
            let mut next = self.iter.next();
            if let Some((next, event)) = next.as_mut() {
                if let Some(next_t) = next.downcast_mut::<T>() {
                    (self.f)(next_t, *event)
                }
            }
            next
        }
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

    impl<'a, T: Any> VisitIter for Single<'a, T> {
        fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
            <Self as LendingIterator>::next(self)
        }
    }

    impl<'a, T: Any> LendingIterator for Single<'a, T> {
        type Item<'b> = (&'b mut dyn Any, Event) where Self: 'b;
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
    pub fn visit<T: Visitable, U: 'static>(obj: &mut T, callback: impl FnMut(&mut U, Event)) {
        obj.visit_iter().inspect_t(callback).run();
    }
}

impl Visitable for u8 {
    type Iter<'a> = Single<'a, u8>;
    fn visit_iter<'a>(&'a mut self) -> Self::Iter<'a> {
        single(self)
    }
}

#[derive(Debug)]
pub struct Point {
    x: u8,
    y: u8,
}

// This can be derived automatically.
impl Visitable for Point {
    type Iter<'a> = PointIter<'a>;
    fn visit_iter<'a>(&'a mut self) -> Self::Iter<'a> {
        PointIter {
            this: self,
            next_step: PointNextStep::EnterSelf,
        }
    }
}
enum PointNextStep {
    EnterSelf,
    EnterX,
    ExitX,
    EnterY,
    ExitY,
    ExitSelf,
    Done,
}
pub struct PointIter<'a> {
    this: &'a mut Point,
    next_step: PointNextStep,
}
impl<'a> VisitIter for PointIter<'a> {
    fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
        <Self as LendingIterator>::next(self)
    }
}
impl<'a> LendingIterator for PointIter<'a> {
    type Item<'b> = (&'b mut dyn Any, Event) where 'a: 'b;
    fn next(&mut self) -> Option<(&mut dyn Any, Event)> {
        // This is in fact a hand-rolled `Generator`. With nightly rustc we might be able
        // to use `yield` to make this even easier to write.
        use Event::*;
        use PointNextStep::*;
        match self.next_step {
            EnterSelf => {
                self.next_step = EnterX;
                Some((self.this as &mut dyn Any, Enter))
            }
            EnterX => {
                self.next_step = ExitX;
                Some((&mut self.this.x as &mut dyn Any, Enter))
            }
            ExitX => {
                self.next_step = EnterY;
                Some((&mut self.this.x as &mut dyn Any, Exit))
            }
            EnterY => {
                self.next_step = ExitY;
                Some((&mut self.this.y as &mut dyn Any, Enter))
            }
            ExitY => {
                self.next_step = ExitSelf;
                Some((&mut self.this.y as &mut dyn Any, Exit))
            }
            ExitSelf => {
                self.next_step = Done;
                Some((self.this as &mut dyn Any, Exit))
            }
            Done => None,
        }
    }
}

fn main() {
    let mut p = Point { x: 42, y: 12 };
    p.visit_iter()
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
