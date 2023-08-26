use crate::formula::NamingInfo;
use crate::formula::{Formula, Term};

use once_cell::sync::Lazy;
use pest::{
    iterators::{Pair, Pairs},
    pratt_parser::PrattParser,
    Parser,
};
use unicode_normalization::UnicodeNormalization;

#[derive(pest_derive::Parser)]
#[grammar = "parser.pest"]
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

pub fn parse(s: &str) {
    let s = s.nfkc().collect::<String>();
    println!("{s}");

    match FormulaParser::parse(Rule::input_formula, &s) {
        Ok(mut pairs) => {
            println!("{:#?}", pairs);
            // let term = parse_term(pairs.next().unwrap());
            // println!("{term:#?}");
            let fml = parse_formula(pairs.next().unwrap().into_inner());
            println!("{fml:#?}");
        }
        Err(e) => {
            println!("Parse failed: {e}");
        }
    }
}

fn parse_formula(pairs: Pairs<Rule>) -> PFormula {
    use PFormula::*;
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            Rule::formula => parse_formula(primary.into_inner()),
            Rule::p_true => True,
            Rule::p_false => False,
            Rule::predicate => {
                let mut pairs = primary.into_inner();
                let name = pairs.next().unwrap().as_str().to_string();
                let terms = match pairs.next() {
                    Some(pair) => pair.into_inner().map(parse_term).collect(),
                    None => vec![],
                };
                Predicate(name, terms)
            }
            _ => unreachable!(),
        })
        .map_infix(|lhs, op, rhs| match op.as_rule() {
            Rule::and => And(Box::new(lhs), Box::new(rhs)),
            Rule::or => Or(Box::new(lhs), Box::new(rhs)),
            Rule::implies => Implies(Box::new(lhs), Box::new(rhs)),
            Rule::iff => Iff(Box::new(lhs), Box::new(rhs)),
            _ => unreachable!(),
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::not => Not(Box::new(rhs)),
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
                    Rule::all => All(bdd_vars, Box::new(rhs)),
                    Rule::exists => Exists(bdd_vars, Box::new(rhs)),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        })
        .parse(pairs)
}

fn parse_term(pair: Pair<Rule>) -> PTerm {
    use PTerm::*;
    let pair = pair.into_inner().next().unwrap();
    match pair.as_rule() {
        Rule::variable => Var(pair.as_str().to_string()),
        Rule::function => {
            let mut pairs = pair.into_inner();
            let name = pairs.next().unwrap().as_str().to_string();
            let terms = pairs.next().unwrap().into_inner().map(parse_term).collect();
            Function(name, terms)
        }
        _ => unreachable!(),
    }
}
