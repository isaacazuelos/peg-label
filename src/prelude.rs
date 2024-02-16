//! A bunch of helpers for defining rules.

pub use crate::{Label, Language, NonTerminal, Parser, Rule, Terminal};

/// ε, the rule which accepts the empty string
pub const fn e<L: Language>() -> Rule<L> {
    Rule::Empty
}

/// terminal t
pub const fn t<L: Language>(token: L::Token) -> Rule<L> {
    Rule::Terminal(token)
}

/// non-terminal n
pub const fn nt<L: Language>(n: L::RuleName) -> Rule<L> {
    Rule::NonTerminal(n)
}

/// p1 p2
pub fn seq<L: Language>(p1: Rule<L>, p2: Rule<L>) -> Rule<L> {
    Rule::Sequence(Box::new((p1, p2)))
}

/// p1 p2 ... pn
pub fn seq_m<L: Language>(ps: &[Rule<L>]) -> Rule<L> {
    match ps {
        [] => panic!("alt_m on empty list of alternates"),
        [p] => p.clone(),
        [p, ps @ ..] => ps.iter().cloned().fold(p.clone(), seq),
    }
}

/// p1 | p2
pub fn alt<L: Language>(p1: Rule<L>, p2: Rule<L>) -> Rule<L> {
    Rule::OrderedChoice(Box::new((p1, p2)))
}

/// p1 | p2 | ... | pn
pub fn alt_m<L: Language>(ps: &[Rule<L>]) -> Rule<L> {
    match ps {
        [] => panic!("alt_m on empty list of alternates"),
        [p] => p.clone(),
        [p, ps @ ..] => ps.iter().cloned().fold(p.clone(), alt),
    }
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
