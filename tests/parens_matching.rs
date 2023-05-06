//! A test of a language which is just matching parens.

use std::collections::HashMap;

use peg_label::prelude::*;

struct L {
    rules: HashMap<&'static str, Rule<Self>>,
    recoveries: HashMap<&'static str, Rule<Self>>,
}

impl Default for L {
    fn default() -> L {
        let rules: HashMap<<Self as Language>::RuleName, Rule<Self>> = [
            (
                "start",
                alt_m(&[e(), nt("paren"), nt("brace"), nt("bracket")]),
            ),
            ("paren", seq_m(&[t('('), t(')')])),
            ("brace", seq_m(&[t('{'), t('}')])),
            ("bracket", seq_m(&[t('['), t(']')])),
        ]
        .into_iter()
        .collect();

        let recoveries = [].into_iter().collect();

        L { rules, recoveries }
    }
}

impl Language for L {
    type Token = char;
    type RuleName = &'static str;

    const START: Self::RuleName = "start";

    fn rule(&self, name: &Self::RuleName) -> &peg_label::Rule<Self> {
        &self.rules[name]
    }

    fn recovery(&self, label: peg_label::Label) -> Option<&peg_label::Rule<Self>> {
        let l = label?;
        self.recoveries.get(l)
    }
}

fn parse(input: &str) -> Result<(), Vec<(usize, Label)>> {
    let lang = L::default();
    let mut p = Parser::new(&lang, input);
    p.parse()
}

#[test]
fn empty() {
    assert!(parse("").is_ok())
}

#[test]
fn simple() {
    assert!(parse("([{()}])").is_ok())
}

#[test]
fn simple_fail() {
    assert!(parse("([{(}])").is_err())
}
