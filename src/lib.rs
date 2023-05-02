//! Peggy, a test for recovering PEG parsers.
//!
//! [Syntax Error Recovery in Parsing Expression Grammars][1]
//!
//! [1]: https://arxiv.org/abs/1806.11150

use std::collections::HashMap;

pub mod prelude;

// An offset into whatever we're parsing.
pub type Cursor = usize;
pub type Terminal = char;
pub type NonTerminal = u32;
pub type Label = Option<u32>;

pub trait Input {
    fn at_cursor(&self, cursor: Cursor) -> Option<Terminal>;
    fn next(&self, cursor: Cursor) -> Cursor;
}

pub struct Out(Result<Cursor, Label>, Option<Cursor>, Vec<(Cursor, Label)>);

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

pub struct Recover {
    pub strategies: HashMap<Label, Rule>,
}

pub struct Grammar<I> {
    input: I,
    rules: HashMap<NonTerminal, Rule>,
    strategies: HashMap<Label, Rule>,
}

impl<I> Grammar<I>
where
    I: Input,
{
    pub fn peek(&self, x: Cursor) -> Option<Terminal> {
        self.input.at_cursor(x)
    }

    pub fn peg(&self, p: &Rule, x: Cursor) -> Out {
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

    fn empty_1(&self, x: Cursor) -> Out {
        Out(Ok(x), None, Vec::new())
    }

    fn terminal(&self, a: Terminal, ax: Cursor) -> Out {
        match self.peek(ax) {
            // term_1
            Some(b) if b == a => Out(Ok(self.input.next(ax)), None, Vec::new()),
            // term_2
            Some(_) => Out(Err(None), Some(ax), Vec::new()),
            // term_3
            None => Out(Err(None), Some(ax), Vec::new()),
        }
    }

    /// both var_1 and var_1
    fn non_terminal(&self, pa: &NonTerminal, x: Cursor) -> Out {
        let a = &self.rules[pa];
        self.peg(a, x)
    }

    /// seq_{1-4}
    fn sequence(&self, p1: &Rule, p2: &Rule, x: Cursor) -> Out {
        let out_1: Out = self.peg(p1, x);

        // seq_4 is when p1 fails or throws
        let Ok(x2) = out_1.0 else  {
            return out_1;
        };

        let out_2 = self.peg(p2, x2);

        if let Err(None) = out_2.0 {
            // seq_2 is when p2 fails
            let mut errors = out_1.2;
            errors.extend(out_2.2);
            Out(Err(None), min(out_1.1, out_2.1), errors)
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

    fn ordered_choice(&self, p1: &Rule, p2: &Rule, x: Cursor) -> Out {
        let mut out_1 = self.peg(p1, x);

        // ord.1
        if out_1.0.is_ok() {
            return out_1;
        }

        // ord.2
        if matches!(out_1.0, Err(Some(_))) {
            return out_1;
        }

        assert_eq!(out_1.0, Err(None));

        let out_2 = self.peg(p2, x);

        // ord.3
        if out_2.0 == Err(None) {
            out_1.2.extend(out_2.2);
            return Out(Err(None), min(out_2.1, out_1.1), out_1.2);
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
    fn repeat(&self, p: &Rule, x: Cursor) -> Out {
        let mut x = x;
        loop {
            let mut out = self.peg(p, x);
            match out.0 {
                Err(None) => {
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
    fn not(&self, rule: &Rule, x: Cursor) -> Out {
        let out = self.peg(rule, x);
        if out.0.is_err() {
            Out(Ok(x), None, Vec::new())
        } else {
            Out(Err(None), None, Vec::new())
        }
    }

    fn throw(&self, l: &Label, x: Cursor) -> Out {
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

fn min(lhs: Option<Cursor>, rhs: Option<Cursor>) -> Option<Cursor> {
    match (lhs, rhs) {
        (Some(l), Some(r)) => Some(l.max(r)),
        (Some(l), None) => Some(l),
        (None, Some(r)) => Some(r),
        _ => None,
    }
}
