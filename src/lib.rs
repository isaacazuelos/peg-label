//! Peggy, a test for recovering PEG parsers.
//!
//! [Syntax Error Recovery in Parsing Expression Grammars][1]
//!
//! [1]: https://arxiv.org/abs/1806.11150

use std::{collections::HashMap, fmt::Debug};

pub mod prelude;

/// An offset into whatever we're parsing.
pub type Cursor = usize;

/// Each 'terminal' symbol, the pieces of input.
///
/// This would typically be something like token type, `char` or `u8`.
///
/// In a rule like `block = '{' statements ' }'`, the `'{'` and `'}'` would be
/// terminals.
///
/// Tokens types could conceivably contain references to associated errata
/// (like whitespace, comments, location tracking info, `&str`, etc.) that we
/// don't necessarily want to use when comparing tokens to some terminal in a
/// rule.
///
/// Each terminal instead can produce a 'Tag' that's used in rules, and for
/// comparison, that doesn't have any of errata.
///
/// So you might have code like this:
///
/// ``` no-run
/// enum Kind { Identifier, OpenParen, CloseParen, Add, Sub, Mul, Div }
/// enum Token { kind: Kind, location: Range<usize> }
///
/// impl TerminalTag for Kind { ... }
/// impl Terminal for Token { type Tag = Kind; ... }
/// ```
pub trait Terminal: Debug + Clone + Copy {
    type Tag: TerminalTag;
    fn tag(&self) -> Self::Tag;
}

pub trait TerminalTag: PartialEq + Clone + Copy {}

/// Each 'non terminal' symbol. These are the names, or the right-hand
/// side of a production rules in a grammar.
///
/// In a rule like `block = '{' statements ' }'`, `block` and `statement` would
/// be non-terminals.
pub type NonTerminal = u32;

/// Labels for errors and their corresponding recovery strategies.
///
/// An option is used here were `None` is the _Fail_ state in the paper -- it
/// signifies that a rule did not succeed, but also consumed no input and
/// produced no errors.
pub type Label = Option<u32>;

/// Input types are indexable sequences of [`Terminal`] values.
///
/// This is nearly, but not quite the same as [`Index<Cursor>`][1], where
/// instead we want to use leverage [`Token`] being `Copy` and not return
/// a reference.
///
/// We also need a way to increment the [`Cursor`] (i.e. a [`usize`]) by more
/// than 1 at a time, so we can support `&str` and it's multi-byte characters.
///
/// [1]: std::ops::Index
pub trait Input {
    type Token: Terminal;
    fn at_cursor(&self, cursor: Cursor) -> Option<Self::Token>;
    fn next(&self, cursor: Cursor) -> Cursor;
}

impl TerminalTag for char {}
impl TerminalTag for u8 {}

impl Terminal for char {
    type Tag = Self;
    fn tag(&self) -> Self::Tag {
        *self
    }
}

impl Terminal for u8 {
    type Tag = Self;
    fn tag(&self) -> Self::Tag {
        *self
    }
}

impl<'a> Input for &'a str {
    type Token = char;

    fn at_cursor(&self, cursor: Cursor) -> Option<Self::Token> {
        self[cursor..].chars().next()
    }

    fn next(&self, cursor: Cursor) -> Cursor {
        cursor + self.at_cursor(cursor).map(char::len_utf8).unwrap_or(1)
    }
}

impl<T: Terminal> Input for &[T] {
    type Token = T;

    fn at_cursor(&self, cursor: Cursor) -> Option<Self::Token> {
        self.get(cursor).cloned()
    }

    fn next(&self, cursor: Cursor) -> Cursor {
        cursor + 1
    }
}

pub type Out = Result<Cursor, Label>;

pub enum Rule<T: Terminal> {
    Empty,
    Terminal(T::Tag),
    NonTerminal(NonTerminal),
    Sequence(Box<(Self, Self)>),
    OrderedChoice(Box<(Self, Self)>),
    Repeat(Box<Self>),
    Not(Box<Self>),
    Throw(Label),
}

pub struct Recover<T> {
    pub strategies: HashMap<Label, T>,
}

pub trait Language {
    type Token: Terminal;
    const START: NonTerminal;

    fn rule(&self, name: &NonTerminal) -> &Rule<Self::Token>;
    fn recovery(&self, label: &Label) -> Option<&Rule<Self::Token>>;
}

pub struct Parser<'l, L, I> {
    language: &'l L,
    input: I,
    furthest: Option<Cursor>,
    errors: Vec<(Cursor, Label)>,
}

impl<'l, L, I, T, K> Parser<'l, L, I>
where
    L: Language<Token = T>,
    I: Input<Token = T>,
    T: Terminal<Tag = K>,
    K: TerminalTag,
{
    pub fn strategy(&self, label: &Label) -> Option<&'l Rule<T>> {
        self.language.recovery(label)
    }

    pub fn peg(&mut self, p: &Rule<T>, x: Cursor) -> Out {
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
        Ok(x)
    }

    fn terminal(&mut self, a: T::Tag, ax: Cursor) -> Out {
        match self.input.at_cursor(ax) {
            // term_1
            Some(b) if b.tag() == a => Ok(self.input.next(ax)),
            // term_2
            Some(_) => {
                self.furthest = Some(ax);
                Err(None)
            }
            // term_3
            None => {
                self.furthest = Some(ax);
                Err(None)
            }
        }
    }

    /// both var_1 and var_1
    fn non_terminal(&mut self, pa: &NonTerminal, x: Cursor) -> Out {
        let a = self.language.rule(pa);
        self.peg(a, x)
    }

    /// seq_{1-4}
    fn sequence(&mut self, p1: &Rule<T>, p2: &Rule<T>, x: Cursor) -> Out {
        let out_1: Out = self.peg(p1, x);

        // seq_4 is when p1 fails or throws
        let Ok(x2) = out_1 else  {
            return out_1;
        };

        let furthest_1 = self.furthest;

        let out_2 = self.peg(p2, x2);

        if let Err(None) = out_2 {
            // seq_2 is when p2 fails
            self.furthest = min(furthest_1, self.furthest);
            Err(None)
        } else if let Err(l) = out_2 {
            // seq_3 is when p2 throws
            Err(l)
        } else {
            // seq_1 is when they both succeed
            assert!(out_1.is_ok() && out_2.is_ok());
            out_2
        }
    }

    fn ordered_choice(&mut self, p1: &Rule<T>, p2: &Rule<T>, x: Cursor) -> Out {
        let out_1 = self.peg(p1, x);

        // ord.1
        if out_1.is_ok() {
            return out_1;
        }

        // ord.2
        if matches!(out_1, Err(Some(_))) {
            return out_1;
        }

        assert_eq!(out_1, Err(None));

        let f1 = self.furthest;
        let out_2 = self.peg(p2, x);
        let f2 = self.furthest;

        self.furthest = min(f1, f2);

        // ord.3
        if out_2 == Err(None) {
            return Err(None);
        }

        // ord.4
        if let Ok(y) = out_2 {
            return Ok(y);
        }

        // ord 5
        out_2
    }

    // This one's a bit different. rep.1 tells us to stop when we hit a
    // [`Label::Fail`] and return the input.
    fn repeat(&mut self, p: &Rule<T>, x: Cursor) -> Out {
        let mut x = x;
        loop {
            let out = self.peg(p, x);
            match out {
                Err(None) => {
                    // If it fails, i.e. consumes nothing, we return what's
                    // left of the input.
                    return Ok(x);
                }
                Err(_) => {
                    // If it throws, we pass that label back up.
                    return out;
                }
                Ok(x2) => {
                    // If it succeeds, we update the cursor and try again.
                    x = x2;
                }
            }
        }
    }

    // not_1 and not_2
    fn not(&mut self, rule: &Rule<T>, x: Cursor) -> Out {
        // We don't want to keep any errors collected while running the rule.
        let errors = self.errors.len();
        let furthest = self.furthest;

        let out = self.peg(rule, x);

        self.errors.truncate(errors);
        self.furthest = furthest;

        match out {
            Ok(_) => Err(None),
            Err(_) => Ok(x),
        }
    }

    fn throw(&mut self, l: Label, x: Cursor) -> Out {
        let Some(recovery) = self.strategy(&l) else {
            // throw_1 is when l is not in R
            self.furthest = Some(x);
            return Err(l);
        };

        let mut out = self.peg(recovery, x);

        if let Err(l2) = out {
            // throw_3
            self.errors.push((x, l));
            out = Err(l2);
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
