//! A bunch of helpers for defining rules.

pub use crate::{Label, Parser, Rule};

/// p1 p2
pub fn seq(p1: Rule, p2: Rule) -> Rule {
    Rule::Sequence(Box::new((p1, p2)))
}

/// p1 | p2
pub fn alt(p1: Rule, p2: Rule) -> Rule {
    Rule::OrderedChoice(Box::new((p1, p2)))
}

/// p*
pub fn star(p: Rule) -> Rule {
    Rule::Repeat(Box::new(p))
}

/// !p
pub fn not(p: Rule) -> Rule {
    Rule::Not(Box::new(p))
}

/// ^label
pub fn throw(label: Label) -> Rule {
    Rule::Throw(label)
}

/// [p]^l, i.e. (p | ^l)
pub fn label(rule: Rule, label: Label) -> Rule {
    Rule::OrderedChoice(Box::new((rule, Rule::Throw(label))))
}
