# type-walker

This is a toy crate that provides an API to visit the fields and sub-fields of a type with an
`Iterator`-like API. It mimics the kind of traversal done by
[derive-visitor](https://crates.io/crates/derive-visitor), but the iterator-like interface is a lot
more flexible to use.

This comes at the cost of type-level hacks, a bit of `unsafe`, and having to work around
borrow-checker limitations.

## Overview

This crate defines a `TypeWalker` trait, which is an iterator over `(&mut dyn Any, Event)`, with:

```rust
pub trait TypeWalker = for<'item> LendingIterator<Item<'item> = (&'item mut dyn Any, Event)>
enum Event {
    Enter,
    Exit,
}
```

A type walker is used to walk over a value and yield references to the various sub-values in
a tree-like fashion:
```rust
struct SomeStruct {
    field1: Type1,
    field2: Type2,
}
// Walking over `s: &mut SomeStruct` will yield:
// (&mut s, Event::Enter)
//   (&mut s.field1, Event::Enter)
//     ... more values for the subvalues of `field1`
//   (&mut s.field1, Event::Exit)
//   (&mut s.field2, Event::Enter)
//     ... more values for the subvalues of `field2`
//   (&mut s.field2, Event::Exit)
// (&mut s, Event::Exit)
```

Note that we can't use normal iterators for that, as we yield mutable references that overlap. To
make this work, we use lending iterators, provided by the
[lending_iterator](https://docs.rs/lending-iterator/latest/lending_iterator/index.html) crate.

The other important trait in this crate is `Walkable`, which denotes a type that can be walked. This
is the equivalent of `IntoIterator` for `TypeWalker`s:

```rust
pub trait Walkable {
    type Walker<'a>: TypeWalker
    where
        Self: 'a;
    fn walk<'a>(&'a mut self) -> Self::Walker<'a>;
}
```

## Usage

`TypeWalker` provides utilities for walking over types. A typical walk uses `TypeWalker::inspect_t`
to catch the events over particular types of interest:

```rust
pub struct Point {
    x: u8,
    y: u8,
}

let mut p = Point { x: 42, y: 12 };
p.walk()
    // This is called each time we visit a `Point`.
    .inspect_t(|p: &mut Point, e| match e {
        Event::Enter => {
            assert_eq!(p.x, 42);
            assert_eq!(p.y, 12);
        }
        Event::Exit => {
            assert_eq!(p.x, 44);
            assert_eq!(p.y, 14);
        }
    })
    // This is called each time we visit a `u8`.
    .inspect_t(|x: &mut u8, _| {
        *x += 1;
    })
    // This consumes the iterator until empty.
    .run_to_completion();

assert_eq!(p.x, 44);
assert_eq!(p.y, 14);
```

We also support shared-state visitors using the `VisitorBuilder` API:

```rust
// Build a visitor with access to `state` that will be called on objects of types `Type1` and
// `Type2`.
let visitor = VisitorBuilder::new_mut(&mut state)
    .on_mut(|state, x: &mut Type1, e| ...)
    .on_mut(|state, x: &mut Type2, e| ...);
// Walk `val` with the visitor.
val.walk().inspect_with(visitor).run_to_completion();
```

## Implementing `Walkable`

This crate does not have derive macros yet. In the mean time, you must implement the traits by hand.
It's not too hard using the utilities provided.

It looks like:
```rust
impl Walkable for SomeStruct {
    type InnerWalker<'a> = impl TypeWalker;
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
        self.field1.walk().chain(self.field2.walk())
    }
}
```

`Walkable::walk()` takes care of yielding `(self, Enter)` and `(self, Exit)` at the start and end.
Your implementation of `walk_inner` must only walk over the inner fields of your type.

For structs, use `LendingIterator::chain` to chain the iterators over each field, like above.
`empty_walker()` can be used for structs without fields.

For enums, use `Either` to handle alternatives with different types. If there are more than two
alternatives, you will have to nest `Either`s.

```rust
pub enum OneOrTwo {
    One(u8),
    Two(SomeStruct),
    Three,
}

impl Walkable for OneOrTwo {
    type InnerWalker<'a> = impl TypeWalker;
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
        match self {
            OneOrTwo::One(one) => Either::Left(Either::Left(single(one))),
            OneOrTwo::Two(two) => Either::Left(Either::Right(two.walk())),
            OneOrTwo::Three => Either::Right(empty_walker()),
        }
    }
}
```
