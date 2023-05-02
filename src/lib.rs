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

pub struct Out(Result<Cursor, Label>);

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

/// We put these in a separate structure so that we can know the language
/// definition doesn't change mid-parse.
pub struct Language {
    rules: HashMap<NonTerminal, Rule>,
    strategies: HashMap<Label, Rule>,
}

pub struct Parser<'l, I> {
    language: &'l Language,
    input: I,
    furthest: Option<Cursor>,
    errors: Vec<(Cursor, Label)>,
}

impl<'l, I> Parser<'l, I>
where
    I: Input,
{
    pub fn strategy(&self, label: Label) -> Option<&'l Rule> {
        self.language.strategies.get(&label)
    }

    pub fn peg(&mut self, p: &Rule, x: Cursor) -> Out {
        match p {
            Rule::Empty => self.empty_1(x),
            Rule::Terminal(a) => self.terminal(*a, x),
            Rule::NonTerminal(pa) => self.non_terminal(pa, x),
            Rule::Sequence(ps) => self.sequence(&ps.0, &ps.1, x),
            Rule::OrderedChoice(ps) => self.ordered_choice(&ps.0, &ps.1, x),
            Rule::Repeat(p) => self.repeat(p, x),
            Rule::Not(p) => self.not(p, x),
            Rule::Throw(l) => self.throw(*l, x),
        }
    }

    fn empty_1(&mut self, x: Cursor) -> Out {
        Out(Ok(x))
    }

    fn terminal(&mut self, a: Terminal, ax: Cursor) -> Out {
        match self.input.at_cursor(ax) {
            // term_1
            Some(b) if b == a => Out(Ok(self.input.next(ax))),
            // term_2
            Some(_) => {
                self.furthest = Some(ax);
                Out(Err(None))
            }
            // term_3
            None => {
                self.furthest = Some(ax);
                Out(Err(None))
            }
        }
    }

    /// both var_1 and var_1
    fn non_terminal(&mut self, pa: &NonTerminal, x: Cursor) -> Out {
        let a = &self.language.rules[pa];
        self.peg(a, x)
    }

    /// seq_{1-4}
    fn sequence(&mut self, p1: &Rule, p2: &Rule, x: Cursor) -> Out {
        let out_1: Out = self.peg(p1, x);

        // seq_4 is when p1 fails or throws
        let Ok(x2) = out_1.0 else  {
            return out_1;
        };

        let furthest_1 = self.furthest;

        let out_2 = self.peg(p2, x2);

        if let Err(None) = out_2.0 {
            // seq_2 is when p2 fails
            self.furthest = min(furthest_1, self.furthest);
            Out(Err(None))
        } else if let Err(l) = out_2.0 {
            // seq_3 is when p2 throws
            Out(Err(l))
        } else {
            // seq_1 is when they both succeed
            assert!(out_1.0.is_ok() && out_2.0.is_ok());
            Out(out_2.0)
        }
    }

    fn ordered_choice(&mut self, p1: &Rule, p2: &Rule, x: Cursor) -> Out {
        let out_1 = self.peg(p1, x);

        // ord.1
        if out_1.0.is_ok() {
            return out_1;
        }

        // ord.2
        if matches!(out_1.0, Err(Some(_))) {
            return out_1;
        }

        assert_eq!(out_1.0, Err(None));

        let f1 = self.furthest;
        let out_2 = self.peg(p2, x);
        let f2 = self.furthest;

        self.furthest = min(f1, f2);

        // ord.3
        if out_2.0 == Err(None) {
            return Out(Err(None));
        }

        // ord.4
        if let Ok(y) = out_2.0 {
            return Out(Ok(y));
        }

        // ord 5
        Out(out_2.0)
    }

    // This one's a bit different. rep.1 tells us to stop when we hit a
    // [`Label::Fail`] and return the input.
    fn repeat(&mut self, p: &Rule, x: Cursor) -> Out {
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
    fn not(&mut self, rule: &Rule, x: Cursor) -> Out {
        // We don't want to keep any errors collected while running the rule.
        let errors = self.errors.len();
        let furthest = self.furthest;

        let out = self.peg(rule, x);

        self.errors.truncate(errors);
        self.furthest = furthest;

        if out.0.is_err() {
            Out(Ok(x))
        } else {
            Out(Err(None))
        }
    }

    fn throw(&mut self, l: Label, x: Cursor) -> Out {
        let Some(recovery) = self.strategy(l) else {
            // throw_1 is when l is not in R
            self.furthest = Some(x);
            return Out(Err(l));
        };

        let mut out = self.peg(recovery, x);

        if let Err(l2) = out.0 {
            // throw_3
            self.errors.push((x, l));
            out.0 = Err(l2);
            out
        } else {
            // throw_2
            self.errors.push((x, l));
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
