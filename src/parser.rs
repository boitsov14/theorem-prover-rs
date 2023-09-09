use crate::formula::{Formula, NamingInfo, Term, FALSE, TRUE};

use once_cell::sync::Lazy;
use unicode_normalization::UnicodeNormalization;

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
    // TODO: 2023/09/06 自由変数をすべてallにする
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

    #[test]
    fn test_parse_term() {
        use PTerm::*;
        assert_eq!(parse_term("x").unwrap(), Var("x".into()));
        assert_eq!(
            parse_term("f(x)").unwrap(),
            Function("f".into(), vec![Var("x".into())])
        );
        assert_eq!(
            parse_term("f(x, y)").unwrap(),
            Function("f".into(), vec![Var("x".into()), Var("y".into())])
        );
        assert_eq!(
            parse_term("f(x, g(y))").unwrap(),
            Function(
                "f".into(),
                vec![Var("x".into()), Function("g".into(), vec![Var("y".into())])]
            )
        );
    }

    #[test]
    fn test_parse_pformula() {
        use PFormula::*;
        use PTerm::*;
        assert_eq!(parse_pformula("true").unwrap(), True);
        assert_eq!(parse_pformula("false").unwrap(), False);
        assert_eq!(parse_pformula("P").unwrap(), Predicate("P".into(), vec![]));
        assert_eq!(
            parse_pformula("P(x)").unwrap(),
            Predicate("P".into(), vec![Var("x".into())])
        );
        assert_eq!(
            parse_pformula("P(x, g(y))").unwrap(),
            Predicate(
                "P".into(),
                vec![Var("x".into()), Function("g".into(), vec![Var("y".into())])]
            )
        );
        assert_eq!(
            parse_pformula("not P").unwrap(),
            Not(Box::new(Predicate("P".into(), vec![])))
        );
        assert_eq!(
            parse_pformula("P and Q").unwrap(),
            And(
                Box::new(Predicate("P".into(), vec![])),
                Box::new(Predicate("Q".into(), vec![]))
            )
        );
        assert_eq!(
            parse_pformula("P or Q").unwrap(),
            Or(
                Box::new(Predicate("P".into(), vec![])),
                Box::new(Predicate("Q".into(), vec![]))
            )
        );
        assert_eq!(
            parse_pformula("P implies Q").unwrap(),
            Implies(
                Box::new(Predicate("P".into(), vec![])),
                Box::new(Predicate("Q".into(), vec![]))
            )
        );
        assert_eq!(
            parse_pformula("P iff Q").unwrap(),
            Iff(
                Box::new(Predicate("P".into(), vec![])),
                Box::new(Predicate("Q".into(), vec![]))
            )
        );
        assert_eq!(
            parse_pformula("all x P(x)").unwrap(),
            All(
                vec!["x".into()],
                Box::new(Predicate("P".into(), vec![Var("x".into())]))
            )
        );
        assert_eq!(
            parse_pformula("all x, y P(x, y)").unwrap(),
            All(
                vec!["x".into(), "y".into()],
                Box::new(Predicate(
                    "P".into(),
                    vec![Var("x".into()), Var("y".into())]
                ))
            )
        );
        assert_eq!(
            parse_pformula("ex x P(x)").unwrap(),
            Exists(
                vec!["x".into()],
                Box::new(Predicate("P".into(), vec![Var("x".into())]))
            )
        );
        assert_eq!(
            parse_pformula("ex x, y P(x, y)").unwrap(),
            Exists(
                vec!["x".into(), "y".into()],
                Box::new(Predicate(
                    "P".into(),
                    vec![Var("x".into()), Var("y".into())]
                ))
            )
        );
    }

    #[test]
    fn test_parse_pformula_assoc() {
        use PFormula::*;
        assert_eq!(
            parse_pformula("P implies Q implies R").unwrap(),
            Implies(
                Box::new(parse_pformula("P").unwrap()),
                Box::new(Implies(
                    Box::new(parse_pformula("Q").unwrap()),
                    Box::new(parse_pformula("R").unwrap())
                ))
            )
        );
    }

    #[test]
    fn test_parse_pformula_precedence() {
        use PFormula::*;
        assert_eq!(parse_pformula("not P and Q or R implies S").unwrap(), {
            let p = parse_pformula("P").unwrap();
            let q = parse_pformula("Q").unwrap();
            let r = parse_pformula("R").unwrap();
            let s = parse_pformula("S").unwrap();
            let np = Not(Box::new(p));
            let np_and_q = And(Box::new(np), Box::new(q));
            let npq_or_r = Or(Box::new(np_and_q), Box::new(r));
            Implies(Box::new(npq_or_r), Box::new(s))
        });
    }
}
