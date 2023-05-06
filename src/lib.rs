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
/// Your token type could conceivably contain references to associated errata
/// (like whitespace, comments, location tracking info, `&str`, etc.) that we
/// don't necessarily want to use when comparing tokens to some terminal in a
/// rule.
///
/// In these cases where you probably don't want to use the full Token type
/// when parsing, you can instead use the [`Input`] implementation for your
/// collection/lexer type to pull out only the important part.
///
/// ``` no-run
/// enum Kind { Identifier, OpenParen, CloseParen, Add, Sub, Mul, Div }
/// enum Token { kind: Kind, location: Range<usize> }
///
/// impl Terminal for Kind {  }
/// impl Input for Vec<Token> { type Token = Kind; ... }
/// ```
pub trait Terminal: Debug + Clone + PartialEq {}

/// Each 'non terminal' symbol. These are the names, or the right-hand
/// side of a production rules in a grammar.
///
/// In a rule like `block = '{' statements ' }'`, `block` and `statement` would
/// be non-terminals.
///
/// You can use numbers for these, or &'static str, if you're not sure where to
/// start when prototyping. A bare `enum` works great too.
pub trait NonTerminal: PartialEq {}

impl NonTerminal for u8 {}
impl NonTerminal for u16 {}
impl NonTerminal for u32 {}
impl NonTerminal for u64 {}
impl NonTerminal for usize {}

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

impl Terminal for char {}
impl Terminal for u8 {}

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

pub enum Rule<L: Language + ?Sized> {
    Empty,
    Terminal(L::Token),
    NonTerminal(L::RuleName),
    Sequence(Box<(Self, Self)>),
    OrderedChoice(Box<(Self, Self)>),
    Repeat(Box<Self>),
    Not(Box<Self>),
    Throw(Label),
}

pub struct Recover<T, L> {
    pub strategies: HashMap<L, T>,
}

pub trait Language {
    type Token: Terminal;
    type RuleName: NonTerminal;
    const START: Self::RuleName;

    fn rule(&self, name: &Self::RuleName) -> &Rule<Self>;
    fn recovery(&self, label: &Label) -> Option<&Rule<Self>>;
}

pub struct Parser<'a, L: Language, I: Input<Token = L::Token>> {
    language: &'a L,
    input: I,
    furthest: Option<Cursor>,
    recovery_status: usize,
    errors: Vec<(Cursor, Label)>,
}

impl<'a, L, I, T> Parser<'a, L, I>
where
    L: Language<Token = T>,
    I: Input<Token = T>,
    T: Terminal,
{
    pub fn strategy(&self, label: &Label) -> Option<&'a Rule<L>> {
        if self.is_recovery_enabled() {
            self.language.recovery(label)
        } else {
            None
        }
    }

    pub fn peg(&mut self, p: &Rule<L>, x: Cursor) -> Result<Cursor, Label> {
        match p {
            Rule::Empty => self.empty_1(x),
            Rule::Terminal(a) => self.terminal(a, x),
            Rule::NonTerminal(pa) => self.non_terminal(pa, x),
            Rule::Sequence(ps) => self.sequence(&ps.0, &ps.1, x),
            Rule::OrderedChoice(ps) => self.ordered_choice(&ps.0, &ps.1, x),
            Rule::Repeat(p) => self.repeat(p, x),
            Rule::Not(p) => self.not(p, x),
            Rule::Throw(l) => self.throw(*l, x),
        }
    }

    fn empty_1(&mut self, x: Cursor) -> Result<Cursor, Label> {
        Ok(x)
    }

    fn terminal(&mut self, a: &L::Token, ax: Cursor) -> Result<Cursor, Label> {
        match self.input.at_cursor(ax) {
            // term_1
            Some(b) if &b == a => Ok(self.input.next(ax)),
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
    fn non_terminal(&mut self, pa: &L::RuleName, x: Cursor) -> Result<Cursor, Label> {
        let a = self.language.rule(pa);
        self.peg(a, x)
    }

    /// seq_{1-4}
    fn sequence(&mut self, p1: &Rule<L>, p2: &Rule<L>, x: Cursor) -> Result<Cursor, Label> {
        let out_1 = self.peg(p1, x);

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

    fn ordered_choice(&mut self, p1: &Rule<L>, p2: &Rule<L>, x: Cursor) -> Result<Cursor, Label> {
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
    fn repeat(&mut self, p: &Rule<L>, x: Cursor) -> Result<Cursor, Label> {
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
    fn not(&mut self, rule: &Rule<L>, x: Cursor) -> Result<Cursor, Label> {
        self.disable_recovery();
        let errors = self.errors.len();
        let furthest = self.furthest;

        let out = self.peg(rule, x);

        self.errors.truncate(errors);
        self.furthest = furthest;
        self.enable_recovery();

        match out {
            Ok(_) => Err(None),
            Err(_) => Ok(x),
        }
    }

    fn throw(&mut self, l: Label, x: Cursor) -> Result<Cursor, Label> {
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

    fn is_recovery_enabled(&self) -> bool {
        self.recovery_status == 0
    }

    fn enable_recovery(&mut self) {
        self.recovery_status -= 1;
    }

    fn disable_recovery(&mut self) {
        self.recovery_status += 1;
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
