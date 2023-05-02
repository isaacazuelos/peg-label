//! Peggy, a test for recovering PEG parsers.
//!
//! [Syntax Error Recovery in Parsing Expression Grammars][1]
//!
//! [1]: https://arxiv.org/abs/1806.11150

use std::collections::HashMap;

// An offset into some &str or &[T] or something that we're parsing.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Input(usize);

impl Input {
    fn next(&self) -> Input {
        Input(1 + self.0)
    }
}

pub type Terminal = char;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Label {
    Fail,
    Other,
}

pub struct Out(Result<Input, Label>, Option<Input>, Vec<(Input, Label)>);

pub enum Rule {
    Empty,
    Terminal(Terminal),
    NonTerminal(NonTerminal),
    Sequence(Box<(Rule, Rule)>),
    OrderedChoice(Box<(Rule, Rule)>),
    Repeat(Box<Rule>),
    Not(Box<Rule>),
    Throw(Label),
}

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

pub struct Recover {
    pub strategies: HashMap<Label, Rule>,
}

type NonTerminal = u32;

pub struct Grammar {
    input: Vec<Terminal>,
    rules: HashMap<NonTerminal, Rule>,
    strategies: HashMap<Label, Rule>,
}

impl Grammar {
    pub fn peek(&self, x: Input) -> Option<Terminal> {
        self.input.get(x.0).cloned()
    }

    pub fn peg(&self, p: &Rule, x: Input) -> Out {
        match p {
            Rule::Empty => self.empty_1(x),
            Rule::Terminal(a) => self.terminal(*a, x),
            Rule::NonTerminal(pa) => self.non_terminal(pa, x),
            Rule::Sequence(ps) => self.sequence(&ps.0, &ps.1, x),
            Rule::OrderedChoice(ps) => self.ordered_choice(&ps.0, &ps.1, x),
            Rule::Repeat(p) => self.repeat(p, x),
            Rule::Not(p) => self.not(p, x),
            Rule::Throw(l) => self.throw(l, x),
        }
    }

    fn empty_1(&self, x: Input) -> Out {
        Out(Ok(x), None, Vec::new())
    }

    fn terminal(&self, a: Terminal, ax: Input) -> Out {
        match self.peek(ax) {
            // term_1
            Some(b) if b == a => Out(Ok(ax.next()), None, Vec::new()),
            // term_2
            Some(_) => Out(Err(Label::Fail), Some(ax), Vec::new()),
            // term_3
            None => Out(Err(Label::Fail), Some(ax), Vec::new()),
        }
    }

    /// both var_1 and var_1
    fn non_terminal(&self, pa: &NonTerminal, x: Input) -> Out {
        let a = &self.rules[pa];
        self.peg(a, x)
    }

    /// seq_{1-4}
    fn sequence(&self, p1: &Rule, p2: &Rule, x: Input) -> Out {
        let out_1: Out = self.peg(p1, x);

        // seq_4 is when p1 fails or throws
        let Ok(x2) = out_1.0 else  {
            return out_1;
        };

        let out_2 = self.peg(p2, x2);

        if let Err(Label::Fail) = out_2.0 {
            // seq_2 is when p2 fails
            let mut errors = out_1.2;
            errors.extend(out_2.2);
            Out(Err(Label::Fail), min(out_1.1, out_2.1), errors)
        } else if let Err(l) = out_2.0 {
            // seq_3 is when p2 throws
            let mut errors = out_1.2;
            errors.extend(out_2.2);
            Out(Err(l), out_2.1, errors)
        } else {
            // seq_1 is when they both succeed
            assert!(out_1.0.is_ok() && out_2.0.is_ok());
            let mut errors = out_1.2;
            errors.extend(out_2.2);
            Out(out_2.0, out_2.1, errors)
        }
    }

    fn ordered_choice(&self, p1: &Rule, p2: &Rule, x: Input) -> Out {
        let mut out_1 = self.peg(p1, x);

        // ord.1
        if out_1.0.is_ok() {
            return out_1;
        }

        // ord.2
        if matches!(out_1.0, Err(l) if l != Label::Fail) {
            return out_1;
        }

        assert_eq!(out_1.0, Err(Label::Fail));

        let out_2 = self.peg(p2, x);

        // ord.3
        if out_2.0 == Err(Label::Fail) {
            out_1.2.extend(out_2.2);
            return Out(Err(Label::Fail), min(out_2.1, out_1.1), out_1.2);
        }

        // ord.4
        if let Ok(y) = out_2.0 {
            out_1.2.extend(out_2.2);
            return Out(Ok(y), min(out_2.1, out_1.1), out_1.2);
        }

        // ord 5
        out_1.2.extend(out_2.2);
        Out(out_2.0, min(out_2.1, out_1.1), out_1.2)
    }

    // This one's a bit different. rep.1 tells us to stop when we hit a
    // [`Label::Fail`] and return the input.
    fn repeat(&self, p: &Rule, x: Input) -> Out {
        let mut x = x;
        loop {
            let mut out = self.peg(p, x);
            match out.0 {
                Err(Label::Fail) => {
                    out.0 = Ok(x);
                    return out;
                }
                Err(_) => {
                    return out;
                }
                Ok(x2) => {
                    x = x2;
                    // todo: We should be keeping errors here.
                }
            }
        }
    }

    // not_1 and not_2
    fn not(&self, rule: &Rule, x: Input) -> Out {
        let out = self.peg(rule, x);
        if out.0.is_err() {
            Out(Ok(x), None, Vec::new())
        } else {
            Out(Err(Label::Fail), None, Vec::new())
        }
    }

    fn throw(&self, l: &Label, x: Input) -> Out {
        let Some(recovery) = self.strategies.get(l) else {
            // throw_1 is when l is not in R
            return Out(Err(*l), Some(x), Vec::new());
        };

        let mut out = self.peg(recovery, x);

        if let Err(l2) = out.0 {
            // throw_3
            out.0 = Err(l2);
            out.2.push((x, *l));
            out
        } else {
            // throw_2
            out.2.push((x, *l));
            out
        }
    }
}

fn min(lhs: Option<Input>, rhs: Option<Input>) -> Option<Input> {
    match (lhs, rhs) {
        (Some(Input(l)), Some(Input(r))) => Some(Input(l.max(r))),
        (Some(l), None) => Some(l),
        (None, Some(r)) => Some(r),
        _ => None,
    }
}
