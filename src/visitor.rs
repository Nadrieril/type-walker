//! Utilities to visit [`crate::Walkable`] types.
use std::any::Any;

use crate::walker::Event;

pub use builder::VisitorBuilder;

/// A stateful visitor. To run it over a [`crate::TypeWalker`], use
/// [`crate::TypeWalker::inspect_with()`].
pub trait TypeVisitor {
    fn visit(&mut self, obj: &mut dyn Any, event: Event);
}

impl<V: TypeVisitor> TypeVisitor for &mut V {
    fn visit(&mut self, obj: &mut dyn Any, event: Event) {
        (**self).visit(obj, event)
    }
}

mod builder {
    use std::any::Any;

    use super::TypeVisitor;
    use crate::walker::Event;

    /// A builder to easily construct stateful visitors.
    ///
    /// Used like:
    /// ```rust,ignore
    /// // Build a visitor with mutable access to `state` that will be called on objects of types
    /// // `Type1` and `Type2`.
    /// let visitor = VisitorBuilder::new(&mut state)
    ///     .on(|state, x: &mut Type1, e| ...)
    ///     .on(|state, x: &mut Type2, e| ...);
    /// // Walk `val` with the visitor.
    /// val.walk().inspect_with(visitor).run_to_completion();
    /// ```
    pub struct VisitorBuilder<'a, S, F> {
        state: &'a mut S,
        visit: F,
    }

    impl<'a, S> VisitorBuilder<'a, S, fn(&mut S, &mut dyn Any, Event)> {
        pub fn new(state: &'a mut S) -> Self {
            Self {
                state,
                visit: |_, _, _| {},
            }
        }
    }

    impl<'a, S, F> VisitorBuilder<'a, S, F>
    where
        F: FnMut(&mut S, &mut dyn Any, Event),
    {
        /// Builds a new visitor that builds on top of this one by additionally calling `f` on any
        /// object of type `T`.
        pub fn on<T: Any>(
            mut self,
            mut t_visitor: impl FnMut(&mut S, &mut T, Event),
        ) -> VisitorBuilder<'a, S, impl FnMut(&mut S, &mut dyn Any, Event)> {
            VisitorBuilder {
                state: self.state,
                visit: move |state: &mut S, obj: &mut dyn Any, event| {
                    (self.visit)(&mut *state, &mut *obj, event);
                    if let Some(obj) = obj.downcast_mut::<T>() {
                        (t_visitor)(state, obj, event)
                    }
                },
            }
        }
    }

    impl<S, F> TypeVisitor for VisitorBuilder<'_, S, F>
    where
        F: FnMut(&mut S, &mut dyn Any, Event),
    {
        fn visit(&mut self, obj: &mut dyn Any, event: Event) {
            (self.visit)(self.state, obj, event)
        }
    }
}
