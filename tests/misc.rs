#![feature(impl_trait_in_assoc_type)]

use type_walker::prelude::*;

#[derive(Debug, PartialEq, Eq)]
pub struct Point {
    x: u8,
    y: u8,
}

// This can be derived automatically.
impl Walkable for Point {
    type InnerWalker<'a> = impl TypeWalker;
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
        single(&mut self.x).chain(single(&mut self.y))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum OneOrTwo {
    One(u8),
    Two(Point),
}

// This can be derived automatically.
impl Walkable for OneOrTwo {
    type InnerWalker<'a> = impl TypeWalker;
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
        match self {
            OneOrTwo::One(one) => Either::Left(single(one)),
            OneOrTwo::Two(two) => Either::Right(two.walk()),
        }
    }
}

#[test]
fn test_inspect() {
    use Event::*;
    let mut p = Point { x: 42, y: 12 };
    p.walk()
        .inspect_t(|p: &mut Point, e| match e {
            Enter => {
                assert_eq!(p.x, 42);
                assert_eq!(p.y, 12);
            }
            Exit => {
                assert_eq!(p.x, 44);
                assert_eq!(p.y, 14);
            }
        })
        .inspect_t(|x: &mut u8, _| {
            *x += 1;
        })
        .run_to_completion();

    assert_eq!(p.x, 44);
    assert_eq!(p.y, 14);
}

#[test]
fn test_visitor_builder() {
    let mut state = 0;
    let visitor = VisitorBuilder::new_mut(&mut state)
        .on_mut(|s, x: &mut u8, _| *s += *x)
        .on_mut(|s, x: &mut u8, _| *s += *x);
    let mut p = Point { x: 42, y: 12 };
    p.walk()
        .only_enter()
        .inspect_with(visitor)
        .run_to_completion();

    assert_eq!(state, 108);
}

#[test]
fn test_nested() {
    let mut one_or_two = OneOrTwo::Two(Point { x: 42, y: 12 });

    let mut walker = one_or_two.walk().filter(|(_, e)| matches!(e, Event::Enter));
    let (x, _) = walker.next_t::<u8>().unwrap();
    *x = 101;
    let (y, _) = walker.next_t::<u8>().unwrap();
    *y = 202;
    assert!(walker.next().is_none());
    drop(walker);

    assert_eq!(one_or_two, OneOrTwo::Two(Point { x: 101, y: 202 }));
}

#[test]
/// Tests iterating over multiple values using the normal `LendingIterator::zip`.
fn test_zip_iter() {
    use Event::*;
    let mut p = Point { x: 10, y: 20 };
    let mut q = Point { x: 100, y: 200 };
    let mut iter = p.walk().zip(q.walk());

    let ((_, Enter), (_, Enter)) = iter.next().unwrap() else {
        panic!()
    };

    let ((p_x, Enter), (q_x, Enter)) = iter.next().unwrap() else {
        panic!()
    };
    let p_x = p_x.downcast_mut::<u8>().unwrap();
    let q_x = q_x.downcast_mut::<u8>().unwrap();
    assert_eq!(*p_x, 10);
    assert_eq!(*q_x, 100);
    *p_x += 1;
    *q_x += 1;

    drop(iter);

    assert_eq!(p.x, 11);
    assert_eq!(q.x, 101);
}

#[test]
/// Tests iterating over multiple values using the special `zip_walkers` API.
fn test_zip_walkers() {
    let mut p = Point { x: 10, y: 20 };
    let mut q = Point { x: 100, y: 200 };
    let mut count_steps = 0;
    let mut zip = zip_walkables([&mut p, &mut q])
        .only_enter()
        .inspect_t::<u8, _>(|_, _| count_steps += 1);

    let ([p_x, q_x], _) = zip.next_t::<u8>().unwrap();
    assert_eq!(*p_x, 10);
    assert_eq!(*q_x, 100);
    *p_x += 1;
    *q_x += 1;

    let _ = zip.next_t::<u8>().unwrap();
    assert!(zip.next_t::<u8>().is_none());

    drop(zip);

    assert_eq!(count_steps, 2);
    assert_eq!(p.x, 11);
    assert_eq!(q.x, 101);
}

/// Illustrates why we can't use a clean GAT-based lending iterator.
#[cfg(any())]
#[test]
fn test_gat_lending_iterator() {
    pub struct RepeatRef<'a, T>(&'a mut T);

    impl<'a, T> gat_lending_iterator::LendingIterator for RepeatRef<'a, T> {
        type Item<'item> = &'item mut T where Self: 'item;
        fn next(&mut self) -> Option<Self::Item<'_>> {
            Some(&mut *self.0)
        }
    }

    // Borrowck limitations force `I: 'static`
    fn zero_all_the_numbers<I>(mut iter: I)
    where
        I: for<'item> gat_lending_iterator::LendingIterator<Item<'item> = &'item mut u32>,
    {
        while let Some(x) = iter.next() {
            *x = 0;
        }
    }

    let mut x = 12;
    // This doesn't work because `RepeatRef` is not `'static`
    zero_all_the_numbers(RepeatRef(&mut x))
}
