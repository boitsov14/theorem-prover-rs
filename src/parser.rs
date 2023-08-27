use crate::formula::NamingInfo;
use crate::formula::{Formula, Term};

use once_cell::sync::Lazy;
use pest::{
    error::Error,
    iterators::{Pair, Pairs},
    pratt_parser::PrattParser,
    Parser,
};
use unicode_normalization::UnicodeNormalization;

#[derive(pest_derive::Parser)]
#[grammar = "grammar.pest"]
struct FormulaParser;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum PTerm {
    Var(String),
    Function(String, Vec<PTerm>),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum PFormula {
    True,
    False,
    Predicate(String, Vec<PTerm>),
    Not(Box<PFormula>),
    And(Box<PFormula>, Box<PFormula>),
    Or(Box<PFormula>, Box<PFormula>),
    Implies(Box<PFormula>, Box<PFormula>),
    Iff(Box<PFormula>, Box<PFormula>),
    All(Vec<String>, Box<PFormula>),
    Exists(Vec<String>, Box<PFormula>),
}

static PRATT_PARSER: Lazy<PrattParser<Rule>> = Lazy::new(|| {
    use pest::pratt_parser::{Assoc::*, Op};
    use Rule::*;
    PrattParser::new()
        .op(Op::infix(iff, Left))
        .op(Op::infix(implies, Left))
        .op(Op::infix(or, Left))
        .op(Op::infix(and, Left))
        .op(Op::prefix(not) | Op::prefix(qf))
});

pub fn example(s: &str) {
    match parse_formula(s) {
        Ok(fml) => {
            println!("{fml:#?}");
        }
        Err(e) => {
            println!("Parse failed: {e}");
        }
    }
}

// TODO: 2023/08/27 convert PFormula to Formula
fn parse_formula(s: &str) -> Result<PFormula, Box<Error<Rule>>> {
    let s: String = s.nfkc().collect();
    let pairs = FormulaParser::parse(Rule::input_formula, &s)?
        .next()
        .unwrap()
        .into_inner();
    Ok(build_formula(pairs))
    // TODO: 2023/08/27 functionやpredicateをquantifyしていないかのチェック
}

fn build_formula(pairs: Pairs<Rule>) -> PFormula {
    use PFormula::*;
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            Rule::formula => build_formula(primary.into_inner()),
            Rule::p_true => True,
            Rule::p_false => False,
            Rule::predicate => {
                let mut pairs = primary.into_inner();
                let name = pairs.next().unwrap().as_str().to_string();
                let terms = match pairs.next() {
                    Some(pair) => pair.into_inner().map(build_term).collect(),
                    None => vec![],
                };
                Predicate(name, terms)
            }
            _ => unreachable!(),
        })
        .map_infix(|p, op, q| match op.as_rule() {
            Rule::and => And(Box::new(p), Box::new(q)),
            Rule::or => Or(Box::new(p), Box::new(q)),
            Rule::implies => Implies(Box::new(p), Box::new(q)),
            Rule::iff => Iff(Box::new(p), Box::new(q)),
            _ => unreachable!(),
        })
        .map_prefix(|op, p| match op.as_rule() {
            Rule::not => Not(Box::new(p)),
            Rule::qf => {
                let mut pairs = op.into_inner();
                let qf_op = pairs.next().unwrap().as_rule();
                let bdd_vars = pairs
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|pair| pair.as_str().to_string())
                    .collect();
                match qf_op {
                    Rule::all => All(bdd_vars, Box::new(p)),
                    Rule::exists => Exists(bdd_vars, Box::new(p)),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        })
        .parse(pairs)
}

fn build_term(pair: Pair<Rule>) -> PTerm {
    use PTerm::*;
    let pair = pair.into_inner().next().unwrap();
    match pair.as_rule() {
        Rule::variable => Var(pair.as_str().to_string()),
        Rule::function => {
            let mut pairs = pair.into_inner();
            let name = pairs.next().unwrap().as_str().to_string();
            let terms = pairs.next().unwrap().into_inner().map(build_term).collect();
            Function(name, terms)
        }
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_term(s: &str) -> Result<PTerm, Box<Error<Rule>>> {
        let pair = FormulaParser::parse(Rule::input_term, s)?.next().unwrap();
        Ok(build_term(pair))
    }
}
