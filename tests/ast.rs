#![feature(impl_trait_in_assoc_type)]
#![feature(box_patterns)]

use std::fmt::Display;

use type_walker::prelude::*;

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

    fn eval(&self) -> u64 {
        match self {
            Expr::Add(a, b) => a.eval() + b.eval(),
            Expr::Mul(a, b) => a.eval() * b.eval(),
            Expr::Num(n) => *n,
        }
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

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum ParentNode {
            Add,
            Mul,
        }
        struct With<'a>(&'a Expr, ParentNode);
        impl Display for With<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let needs_parens = match self {
                    With(Expr::Add(..), ParentNode::Mul) => true,
                    With(Expr::Mul(..), ParentNode::Add) => false,
                    _ => false,
                };
                if needs_parens {
                    write!(f, "({})", self.0)
                } else {
                    write!(f, "{}", self.0)
                }
            }
        }

        match self {
            Expr::Add(a, b) => write!(
                f,
                "{} + {}",
                With(a, ParentNode::Add),
                With(b, ParentNode::Add)
            ),
            Expr::Mul(a, b) => write!(
                f,
                "{} * {}",
                With(a, ParentNode::Mul),
                With(b, ParentNode::Mul)
            ),
            Expr::Num(n) => write!(f, "{n}"),
        }
    }
}

impl Walkable for Expr {
    type InnerWalker<'a> = impl TypeWalker;
    fn walk_inner<'a>(&'a mut self) -> Self::InnerWalker<'a> {
        match self {
            Self::Add(a, b) => Either::Left(Either::Left(a.walk().chain(b.walk()))),
            Self::Mul(a, b) => Either::Left(Either::Right(a.walk().chain(b.walk()))),
            Self::Num(_) => Either::Right(empty_walker()),
        }
    }
}

#[test]
fn test_ast() {
    let num = |x| Expr::num(x);
    let mut tree = num(42).mul(num(1).add(num(2).add(num(3))));
    assert_eq!(tree.eval(), 252);
    assert_eq!(tree.to_string(), "42 * (1 + 2 + 3)");

    tree.walk()
        .inspect_enter(Expr::distribute)
        .run_to_completion();

    assert_eq!(tree.eval(), 252);
    assert_eq!(tree.to_string(), "42 * 1 + 42 * 2 + 42 * 3");
}
