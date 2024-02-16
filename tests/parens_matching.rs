//! A test of a language which is just matching parens.

use std::collections::HashMap;

use peg_label::prelude::*;

#[derive(Debug)]
struct L {
    rules: HashMap<&'static str, Rule<Self>>,
    recoveries: HashMap<&'static str, Rule<Self>>,
}

impl Default for L {
    fn default() -> L {
        let rules: HashMap<<Self as Language>::RuleName, Rule<Self>> = [
            (
                "start",
                alt_m(&[nt("paren"), nt("brace"), nt("bracket"), e()]),
            ),
            (
                "paren",
                seq_m(&[
                    t('('),
                    nt("start"),
                    label(t(')'), Some("missing_close_paren")),
                ]),
            ),
            (
                "brace",
                seq_m(&[
                    t('{'),
                    nt("start"),
                    label(t('}'), Some("missing_close_brace")),
                ]),
            ),
            (
                "bracket",
                seq_m(&[
                    t('['),
                    nt("start"),
                    label(t(']'), Some("missing_close_bracket")),
                ]),
            ),
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

    fn rule(&self, name: Self::RuleName) -> &peg_label::Rule<Self> {
        &self.rules[name]
    }

    fn recovery(&self, label: peg_label::Label) -> Option<&peg_label::Rule<Self>> {
        let l = label?;
        self.recoveries.get(l)
    }
}

#[test]
fn empty() {
    let input = "";
    let lang = L::default();
    let mut p = Parser::new(&lang, input);
    let result = p.parse();
    assert!(result.is_ok(), "result was {:?}", result);
}

#[test]
fn simple() {
    let input = "([{()}])";
    let lang = L::default();
    let mut p = Parser::new(&lang, input);
    let result = p.parse();
    assert!(result.is_ok(), "result was {:?}", result);
}

#[test]
fn simple_fail() {
    let input = "([{(}])";
    let lang = L::default();
    let mut p = Parser::new(&lang, input);
    let result = p.parse();
    assert!(
        result.is_err(),
        "result was {:?} from parser {:?}",
        result,
        p
    );
}
