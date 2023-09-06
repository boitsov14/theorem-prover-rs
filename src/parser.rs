use crate::formula::{Formula, NamingInfo, Term, FALSE, TRUE};

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

pub fn parse_formula(s: &str) -> Result<(Formula, NamingInfo), String> {
    let s: String = s.nfkc().collect();
    // TODO: 2023/08/28 括弧の左右の個数のチェック
    let pfml = match parse_pformula(&s) {
        Ok(pfml) => pfml,
        Err(e) => {
            return Err(e.to_string());
        }
    };
    let (fml, inf) = pfml.into_formula();
    Ok((fml, inf))
    // TODO: 2023/08/27 functionやpredicateをquantifyしていないかのチェック
}

fn parse_pformula(s: &str) -> Result<PFormula, Box<Error<Rule>>> {
    let pairs = FormulaParser::parse(Rule::input_formula, s)?
        .next()
        .unwrap()
        .into_inner();
    Ok(build_formula(pairs))
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
                let name = pairs.next().unwrap().as_str().into();
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
                    .map(|pair| pair.as_str().into())
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
        Rule::variable => Var(pair.as_str().into()),
        Rule::function => {
            let mut pairs = pair.into_inner();
            let name = pairs.next().unwrap().as_str().into();
            let terms = pairs.next().unwrap().into_inner().map(build_term).collect();
            Function(name, terms)
        }
        _ => unreachable!(),
    }
}

impl PTerm {
    fn into_term(self, inf: &mut NamingInfo) -> Term {
        match self {
            PTerm::Var(name) => Term::Var(inf.get_id(name)),
            PTerm::Function(name, pterms) => Term::Function(
                inf.get_id(name),
                pterms
                    .into_iter()
                    .map(|pterm| pterm.into_term(inf))
                    .collect(),
            ),
        }
    }
}

impl PFormula {
    fn into_formula(self) -> (Formula, NamingInfo) {
        let mut inf = NamingInfo::new();
        let fml = self.into_formula_rec(&mut inf);
        (fml, inf)
    }

    fn into_formula_rec(self, inf: &mut NamingInfo) -> Formula {
        match self {
            PFormula::True => TRUE.clone(),
            PFormula::False => FALSE.clone(),
            PFormula::Predicate(name, pterms) => Formula::Predicate(
                inf.get_id(name),
                pterms
                    .into_iter()
                    .map(|pterm| pterm.into_term(inf))
                    .collect(),
            ),
            PFormula::Not(p) => Formula::Not(Box::new(p.into_formula_rec(inf))),
            PFormula::And(p, q) => {
                use Formula::And;
                let p = p.into_formula_rec(inf);
                let q = q.into_formula_rec(inf);
                match (p, q) {
                    (And(mut ps), And(qs)) => {
                        ps.extend(qs);
                        And(ps)
                    }
                    (And(mut ps), q) => {
                        ps.push(q);
                        And(ps)
                    }
                    (p, And(mut qs)) => {
                        qs.insert(0, p);
                        And(qs)
                    }
                    (p, q) => And(vec![p, q]),
                }
            }
            PFormula::Or(p, q) => {
                use Formula::Or;
                let p = p.into_formula_rec(inf);
                let q = q.into_formula_rec(inf);
                match (p, q) {
                    (Or(mut ps), Or(qs)) => {
                        ps.extend(qs);
                        Or(ps)
                    }
                    (Or(mut ps), q) => {
                        ps.push(q);
                        Or(ps)
                    }
                    (p, Or(mut qs)) => {
                        qs.insert(0, p);
                        Or(qs)
                    }
                    (p, q) => Or(vec![p, q]),
                }
            }
            PFormula::Implies(p, q) => Formula::Implies(
                Box::new(p.into_formula_rec(inf)),
                Box::new(q.into_formula_rec(inf)),
            ),
            PFormula::Iff(p, q) => Formula::Iff(
                Box::new(p.into_formula_rec(inf)),
                Box::new(q.into_formula_rec(inf)),
            ),
            PFormula::All(names, p) => Formula::All(
                names.into_iter().map(|name| inf.get_id(name)).collect(),
                Box::new(p.into_formula_rec(inf)),
            ),
            PFormula::Exists(names, p) => Formula::Exists(
                names.into_iter().map(|name| inf.get_id(name)).collect(),
                Box::new(p.into_formula_rec(inf)),
            ),
        }
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
