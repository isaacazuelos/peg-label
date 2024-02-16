use std::ops::Range;

use lazy_static::lazy_static;

use peg_label::{prelude::*, Cursor, Input};

#[derive(Debug, Clone, PartialEq, Copy)]
enum Kind {
    Class,
    LBra,
    RBra,
    LCur,
    RCur,
    LPar,
    RPar,
    Main,
    Name,
    Public,
    Static,
    String,
    Void,

    Int,
    Assign,
    Print,
    Semi,
    Number,
    Eq,
    Lt,
    Plus,
    Minus,
    Times,
    Div,
}

struct Token {
    kind: Kind,
    location: Range<usize>,
}

impl Terminal for Kind {}

struct Tokens(Vec<Token>);

impl Input for Tokens {
    type Token = Kind;

    fn at_cursor(&self, cursor: Cursor) -> Option<Self::Token> {
        self.0.get(cursor).map(|t| t.kind)
    }

    fn next(&self, cursor: Cursor) -> Cursor {
        cursor + 1
    }
}

#[repr(usize)]
#[derive(Debug, Copy, Clone, PartialEq)]
enum JavaRuleName {
    Prog,
    BlockStmt,
    Stmt,
    IfStmt,
    WhileStmt,
    DecStmt,
    AssignStmt,
    PrintStmt,
    Exp,
    RelExp,
    AddExp,
    MulExp,
    AtomExp,
}

impl NonTerminal for JavaRuleName {}

#[derive(Debug)]
struct JavaSubset;

impl Language for JavaSubset {
    type Token = Kind;
    type RuleName = JavaRuleName;

    const START: Self::RuleName = JavaRuleName::Prog;

    fn rule(&self, name: Self::RuleName) -> &Rule<Self> {
        &RULES[name as usize]
    }

    fn recovery(&self, label: Label) -> Option<&Rule<Self>> {
        todo!()
    }
}

lazy_static! {
    static ref RULES: Vec<Rule<JavaSubset>> = vec![
        // Prog
        seq_m(&[
            t(Kind::Public),
            t(Kind::Class),
            t(Kind::Name),
            t(Kind::LCur),
            t(Kind::Public),
            t(Kind::Static),
            t(Kind::Void),
            t(Kind::Main),
            t(Kind::LPar),
            t(Kind::String),
            t(Kind::LBra),
            t(Kind::RBra),
            t(Kind::Name),
            t(Kind::RPar),
            nt(JavaRuleName::BlockStmt),
            t(Kind::RCur),
        ]),
        // BlockStmt
        seq_m(&[
            t(Kind::LCur),
            star(nt(JavaRuleName::Stmt)),
            label(t(Kind::RCur), Some("rcblk")),
        ])
    ];
}

fn main() {
    todo!("this example is incomplete")
}
