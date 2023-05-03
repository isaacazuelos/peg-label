//! A bunch of helpers for defining rules.

pub use crate::{Label, Language, NonTerminal, Parser, Rule, Terminal};

/// p1 p2
pub fn seq<L: Language>(p1: Rule<L>, p2: Rule<L>) -> Rule<L> {
    Rule::Sequence(Box::new((p1, p2)))
}

/// p1 | p2
pub fn alt<L: Language>(p1: Rule<L>, p2: Rule<L>) -> Rule<L> {
    Rule::OrderedChoice(Box::new((p1, p2)))
}

/// p*
pub fn star<L: Language>(p: Rule<L>) -> Rule<L> {
    Rule::Repeat(Box::new(p))
}

/// !p
pub fn not<L: Language>(p: Rule<L>) -> Rule<L> {
    Rule::Not(Box::new(p))
}

/// ^label
pub fn throw<L: Language>(label: Label) -> Rule<L> {
    Rule::Throw(label)
}

/// [p]^l, i.e. (p | ^l)
pub fn label<L: Language>(rule: Rule<L>, label: Label) -> Rule<L> {
    Rule::OrderedChoice(Box::new((rule, Rule::Throw(label))))
}
