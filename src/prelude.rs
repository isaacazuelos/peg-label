//! A bunch of helpers for defining rules.

use crate::Terminal;
pub use crate::{Label, Parser, Rule};

/// p1 p2
pub fn seq<T: Terminal>(p1: Rule<T>, p2: Rule<T>) -> Rule<T> {
    Rule::Sequence(Box::new((p1, p2)))
}

/// p1 | p2
pub fn alt<T: Terminal>(p1: Rule<T>, p2: Rule<T>) -> Rule<T> {
    Rule::OrderedChoice(Box::new((p1, p2)))
}

/// p*
pub fn star<T: Terminal>(p: Rule<T>) -> Rule<T> {
    Rule::Repeat(Box::new(p))
}

/// !p
pub fn not<T: Terminal>(p: Rule<T>) -> Rule<T> {
    Rule::Not(Box::new(p))
}

/// ^label
pub fn throw<T: Terminal>(label: Label) -> Rule<T> {
    Rule::Throw(label)
}

/// [p]^l, i.e. (p | ^l)
pub fn label<T: Terminal>(rule: Rule<T>, label: Label) -> Rule<T> {
    Rule::OrderedChoice(Box::new((rule, Rule::Throw(label))))
}
