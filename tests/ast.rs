#![feature(impl_trait_in_assoc_type)]
#![feature(box_patterns)]

use type_walker::{
    lending_iterator::{Either, LendingIterator},
    walker::{empty_walker, InnerWalkable, TypeWalker, Walkable},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Num(u64),
}

impl Expr {
    fn num(x: u64) -> Self {
        Expr::Num(x)
    }
    fn add(self, other: Self) -> Self {
        Expr::Add(Box::new(self), Box::new(other))
    }
    fn mul(self, other: Self) -> Self {
        Expr::Mul(Box::new(self), Box::new(other))
    }

    /// Distribute multiplication over addition.
    fn distribute(&mut self) {
        use Expr::*;
        match self {
            Mul(box _, box Add(_, _)) => take_mut::take(self, |this| {
                let Mul(box m, box Add(box a, box b)) = this else {
                    unreachable!()
                };
                m.clone().mul(a).add(m.mul(b))
            }),
            Mul(box Add(_, _), box _) => take_mut::take(self, |this| {
                let Mul(box Add(box a, box b), box m) = this else {
                    unreachable!()
                };
                a.mul(m.clone()).add(b.mul(m))
            }),
            _ => {}
        }
    }
}

impl InnerWalkable for Expr {
    type InnerWalker<'a> = impl TypeWalker;
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
        match self {
            Self::Add(a, b) => Either::Left(Either::Left(a.walk().chain(b.walk()))),
            Self::Mul(a, b) => Either::Left(Either::Right(a.walk().chain(b.walk()))),
            Self::Num(_) => Either::Right(empty_walker()),
        }
    }
}
impl Walkable for Expr {
    type Walker<'a> = impl TypeWalker;
    fn walk<'a>(&'a mut self) -> Self::Walker<'a> {
        self.walk_this_and_inside()
    }
}

#[test]
fn test_ast() {
    let num = |x| Expr::num(x);
    let mut tree = num(0).mul(num(1).add(num(2).add(num(3))));
    tree.walk()
        .inspect_enter(Expr::distribute)
        .run_to_completion();
    assert_eq!(
        tree,
        num(0)
            .mul(num(1))
            .add(num(0).mul(num(2)).add(num(0).mul(num(3))))
    );
}
