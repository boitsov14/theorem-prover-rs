use crate::formula::{Formula, Term};
use crate::naming::EntitiesInfo;
use indexmap::IndexSet;
use itertools::Itertools;
use maplit::{hashmap, hashset};
use peg::{error, str::LineCol};
use regex::Regex;
use std::collections::{HashMap, HashSet};
use thiserror::Error;
use unicode_normalization::UnicodeNormalization;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Found {lp} left parentheses and {rp} right parentheses.")]
    Parentheses { lp: usize, rp: usize },
    #[error("
 | 
 | {s}
 | {}^___
 | 
 = expected {}", " ".repeat(e.location.column - 1), e.expected)]
    Core {
        s: String,
        e: error::ParseError<LineCol>,
    },
    #[error("The same name of predicates must take the same number of arguments.")]
    PredicateArity,
    #[error("The same name of functions must take the same number of arguments.")]
    FunctionArity,
    #[error("Cannot quantify predicates.")]
    BddPredicate,
    #[error("Cannot quantify functions.")]
    BddFunction,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PTerm {
    Var(String),
    Function(String, Vec<PTerm>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PFormula {
    Predicate(String, Vec<PTerm>),
    Not(Box<PFormula>),
    And(Vec<PFormula>),
    Or(Vec<PFormula>),
    Implies(Box<PFormula>, Box<PFormula>),
    All(IndexSet<String>, Box<PFormula>),
    Exists(IndexSet<String>, Box<PFormula>),
}

pub static P_TRUE: PFormula = PFormula::And(vec![]);
pub static P_FALSE: PFormula = PFormula::Or(vec![]);

pub fn parse(s: &str) -> Result<(Formula, EntitiesInfo), ParseError> {
    let s = s.nfkc().collect::<String>().trim().to_string();
    let s = Regex::new(r"\s").unwrap().replace_all(&s, " ");
    let lp = s.chars().filter(|&c| c == '(').count();
    let rp = s.chars().filter(|&c| c == ')').count();
    if lp != rp {
        return Err(ParseError::Parentheses { lp, rp });
    }
    let pfml = match parser::formula(&s) {
        Ok(pfml) => pfml,
        Err(e) => {
            let s = s.into();
            return Err(ParseError::Core { s, e });
        }
    };
    let (fml, entities) = pfml.into_formula();
    fml.check()?;
    Ok((fml, entities))
}

pub fn from_tptp(s: &str) -> String {
    let s = s
        .lines()
        .filter(|line| !line.trim_start().starts_with('%'))
        .collect::<String>();

    let mut axioms = vec![];

    let re_axiom = Regex::new(r"fof\(([^,]+),axiom,(.+?)\)\.").unwrap();
    for cap in re_axiom.captures_iter(&s) {
        axioms.push(cap[2].trim().to_string());
    }

    let re_conjecture = Regex::new(r"fof\(([^,]+),conjecture,(.+?)\)\.").unwrap();
    let cap = re_conjecture.captures(&s).unwrap();
    let conjecture = cap[2].trim().to_string();

    axioms
        .iter()
        .rev()
        .fold(conjecture, |acc, axiom| format!("({axiom}) -> ({acc})"))
        .replace('$', "")
}

peg::parser!( grammar parser() for str {
    use PFormula::*;
    use PTerm::*;

    /// Parse a term.
    pub rule term() -> PTerm = quiet!{
        f:$function_name() _ "(" _ ts:(term() ++ (_ "," _)) _ ")" { Function(f.to_string(), ts) } /
        v:$var() { Var(v.to_string()) } /
        "(" t:term() ")" { t }
    } / expected!("term")

    rule predicate() -> PFormula =
        p_true() { P_TRUE.clone() } /
        p_false() { P_FALSE.clone() } /
        p:$predicate_name() _ "(" _ ts:(term() ++ (_ "," _)) _ ")" { Predicate(p.to_string(), ts) } /
        p:$predicate_name() { Predicate(p.to_string(), vec![]) }

    /// Parse a formula.
    /// Every infix operator is right-associative.
    /// The precedence of operators is as follows: not, all, exists > and > or > implies > iff.
    pub rule formula() -> PFormula = precedence!{
        p:@ _ iff() _ q:(@) { And(vec![Implies(Box::new(p.clone()), Box::new(q.clone())), Implies(Box::new(q), Box::new(p))]) }
        --
        p:@ _ implies() _ q:(@) { Implies(Box::new(p), Box::new(q)) }
        --
        p:@ _ or() _ q:(@) {
            match (p, q) {
                (Or(mut ps), Or(qs)) => {
                    ps.extend(qs);
                    Or(ps)
                }
                (Or(mut ps), q) => {
                    if ps.is_empty() {
                        q
                    } else {
                        ps.push(q);
                        Or(ps)
                    }
                }
                (p, Or(mut qs)) => {
                    if qs.is_empty() {
                        p
                    } else {
                        qs.insert(0, p);
                        Or(qs)
                    }
                }
                (p, q) => Or(vec![p, q]),
            }
        }
        --
        p:@ _ and() _ q:(@) {
            match (p, q) {
                (And(mut ps), And(qs)) => {
                    ps.extend(qs);
                    And(ps)
                }
                (And(mut ps), q) => {
                    if ps.is_empty() {
                        q
                    } else {
                        ps.push(q);
                        And(ps)
                    }
                }
                (p, And(mut qs)) => {
                    if qs.is_empty() {
                        p
                    } else {
                        qs.insert(0, p);
                        And(qs)
                    }
                }
                (p, q) => And(vec![p, q]),
            }
        }
        --
        not() _ p:@ { Not(Box::new(p)) }
        all() _ vs:($var() ++ (_ "," _)) _ p:@ {
            let mut vs = vs.iter().map(|&s| s.to_string()).collect::<IndexSet<_>>();
            match p {
                All(ws, q) => {
                    vs.extend(ws);
                    All(vs, q)
                }
                p => All(vs, Box::new(p)),
            }
        }
        exists() _ vs:($var() ++ (_ "," _)) _ p:@ {
            let mut vs = vs.iter().map(|&s| s.to_string()).collect::<IndexSet<_>>();
            match p {
                Exists(ws, q) => {
                    vs.extend(ws);
                    Exists(vs, q)
                }
                p => Exists(vs, Box::new(p)),
            }
        }
        --
        p:predicate() { p }
        "(" _ p:formula() _ ")" { p }
    } / expected!("formula")

    rule ALPHA() = ['a'..='z' | 'A'..='Z' ]
    rule DIGIT() = ['0'..='9' | '_' | '\'' ]
    rule ALPHANUMERIC() = ALPHA() / DIGIT()

    rule var() = ALPHA() DIGIT()*
    rule function_name() = ALPHA() ALPHANUMERIC()*
    rule predicate_name() = quiet!{ ALPHA() ALPHANUMERIC()* } / expected!("predicate")

    rule p_true() = quiet!{ "⊤" / "true" / "tautology" / "top" } / expected!("true")
    rule p_false() = quiet!{ "⊥" / "⟂" / "false" / "contradiction" / "bottom" / "bot" } / expected!("false")

    rule not() = quiet!{ "¬" / "~" / "not" / "lnot" / "negation" / "neg" } / expected!("not")
    rule and() = quiet!{ "∧" / r"/\" / "&&" / "&" / "and" / "land" / "wedge" } / expected!("and")
    rule or() = quiet!{ "∨" / r"\/" / "||" / "|" / "or" / "lor" / "vee" } / expected!("or")
    rule implies() = quiet!{ "→" / "->" / "=>" / "-->" / "==>" / "⇒" / "to" / "implies" / "imply" / "imp" / "rightarrow" } / expected!("implies")
    rule iff() = quiet!{ "↔" / "<->" / "<=>" / "<-->" / "<==>" / "⇔" / "≡" / "iff" / "equivalent" / "equiv" / "leftrightarrow" } / expected!("iff")
    rule all() = quiet!{ "∀" / "!" / "forall" / "all" } / expected!("all")
    rule exists() = quiet!{ "∃" / "?" / "exists" / "ex" } / expected!("exists")

    rule _ = quiet!{ [' ']* }
});

impl PTerm {
    fn into_term(self, entities: &mut EntitiesInfo) -> Term {
        match self {
            Self::Var(name) => Term::Var(entities.get_id(name)),
            Self::Function(name, pterms) => Term::Func(
                entities.get_id(name),
                pterms
                    .into_iter()
                    .map(|pterm| pterm.into_term(entities))
                    .collect(),
            ),
        }
    }
}

impl PFormula {
    fn into_formula(self) -> (Formula, EntitiesInfo) {
        let mut entities = EntitiesInfo::new();
        let fml = self.into_formula_rec(&mut entities);
        (fml, entities)
    }

    fn into_formula_rec(self, entities: &mut EntitiesInfo) -> Formula {
        match self {
            Self::Predicate(name, pterms) => Formula::Predicate(
                entities.get_id(name),
                pterms
                    .into_iter()
                    .map(|pterm| pterm.into_term(entities))
                    .collect(),
            ),
            Self::Not(p) => Formula::Not(Box::new(p.into_formula_rec(entities))),
            Self::And(l) => Formula::And(
                l.into_iter()
                    .map(|p| p.into_formula_rec(entities))
                    .collect(),
            ),
            Self::Or(l) => Formula::Or(
                l.into_iter()
                    .map(|p| p.into_formula_rec(entities))
                    .collect(),
            ),
            Self::Implies(p, q) => Formula::Implies(
                Box::new(p.into_formula_rec(entities)),
                Box::new(q.into_formula_rec(entities)),
            ),
            Self::All(names, p) => Formula::All(
                names
                    .into_iter()
                    .map(|name| entities.get_id(name))
                    .collect(),
                Box::new(p.into_formula_rec(entities)),
            ),
            Self::Exists(names, p) => Formula::Exists(
                names
                    .into_iter()
                    .map(|name| entities.get_id(name))
                    .collect(),
                Box::new(p.into_formula_rec(entities)),
            ),
        }
    }
}

impl Term {
    fn check(
        &self,
        bdd_vars: &HashSet<usize>,
        fns: &mut HashMap<usize, usize>,
    ) -> Result<(), ParseError> {
        use Term::*;
        match self {
            Var(_) => {}
            Func(id, terms) => {
                // check the arity of the function
                if let Some(arity) = fns.get(id) {
                    if *arity != terms.len() {
                        return Err(ParseError::FunctionArity);
                    }
                } else {
                    fns.insert(*id, terms.len());
                }
                // check if the function is quantified
                if bdd_vars.contains(id) {
                    return Err(ParseError::BddFunction);
                }
                for term in terms {
                    term.check(bdd_vars, fns)?;
                }
            }
        }
        Ok(())
    }
}

impl Formula {
    fn check(&self) -> Result<(), ParseError> {
        self.check_rec(hashset![], &mut hashmap![], &mut hashmap![])
    }

    fn check_rec(
        &self,
        mut bdd_vars: HashSet<usize>,
        fns: &mut HashMap<usize, usize>,
        preds: &mut HashMap<usize, usize>,
    ) -> Result<(), ParseError> {
        use Formula::*;
        match self {
            Predicate(id, terms) => {
                for term in terms {
                    term.check(&bdd_vars, fns)?;
                }
                // check the arity of the predicate
                if let Some(arity) = preds.get(id) {
                    if *arity != terms.len() {
                        return Err(ParseError::PredicateArity);
                    }
                } else {
                    preds.insert(*id, terms.len());
                }
                // check if the predicate is quantified
                if bdd_vars.contains(id) {
                    return Err(ParseError::BddPredicate);
                }
            }
            Not(p) => p.check_rec(bdd_vars, fns, preds)?,
            And(l) | Or(l) => {
                for p in l {
                    p.check_rec(bdd_vars.clone(), fns, preds)?;
                }
            }
            Implies(p, q) => {
                p.check_rec(bdd_vars.clone(), fns, preds)?;
                q.check_rec(bdd_vars, fns, preds)?;
            }
            All(vs, p) | Exists(vs, p) => {
                bdd_vars.extend(vs);
                p.check_rec(bdd_vars, fns, preds)?;
            }
        }
        Ok(())
    }

    pub fn universal_quantify(self) -> Self {
        use Formula::All;
        let mut fv = self.free_vars().into_iter().collect_vec();
        if fv.is_empty() {
            return self;
        }
        match self {
            All(vs, p) => {
                fv.extend(vs);
                All(fv, p)
            }
            p => All(fv, Box::new(p)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use indexmap::indexset;
    use parser::{formula, term};

    #[test]
    fn test_parse_term() {
        use PTerm::*;
        assert_eq!(term("x").unwrap(), Var("x".into()));
        assert_eq!(
            term("f(x)").unwrap(),
            Function("f".into(), vec![Var("x".into())])
        );
        assert_eq!(
            term("f(x, g(y), z)").unwrap(),
            Function(
                "f".into(),
                vec![
                    Var("x".into()),
                    Function("g".into(), vec![Var("y".into())]),
                    Var("z".into())
                ]
            )
        );
    }

    #[test]
    fn test_parse_pformula() {
        use PFormula::*;
        use PTerm::*;
        assert_eq!(formula("true").unwrap(), P_TRUE);
        assert_eq!(formula("false").unwrap(), P_FALSE);
        assert_eq!(formula("P").unwrap(), Predicate("P".into(), vec![]));
        assert_eq!(
            formula("P(x)").unwrap(),
            Predicate("P".into(), vec![Var("x".into())])
        );
        assert_eq!(
            formula("P(x, g(y), z)").unwrap(),
            Predicate(
                "P".into(),
                vec![
                    Var("x".into()),
                    Function("g".into(), vec![Var("y".into())]),
                    Var("z".into())
                ]
            )
        );
        assert_eq!(
            formula("not P").unwrap(),
            Not(Box::new(Predicate("P".into(), vec![])))
        );
        assert_eq!(
            formula("P and Q").unwrap(),
            And(vec![
                Predicate("P".into(), vec![]),
                Predicate("Q".into(), vec![])
            ])
        );
        assert_eq!(
            formula("P or Q").unwrap(),
            Or(vec![
                Predicate("P".into(), vec![]),
                Predicate("Q".into(), vec![])
            ])
        );
        assert_eq!(
            formula("P implies Q").unwrap(),
            Implies(
                Box::new(Predicate("P".into(), vec![])),
                Box::new(Predicate("Q".into(), vec![]))
            )
        );
        assert_eq!(
            formula("P iff Q").unwrap(),
            And(vec![
                Implies(
                    Box::new(Predicate("P".into(), vec![])),
                    Box::new(Predicate("Q".into(), vec![]))
                ),
                Implies(
                    Box::new(Predicate("Q".into(), vec![])),
                    Box::new(Predicate("P".into(), vec![]))
                )
            ])
        );
        assert_eq!(
            formula("all x P(x)").unwrap(),
            All(
                indexset!["x".into()],
                Box::new(Predicate("P".into(), vec![Var("x".into())]))
            )
        );
        assert_eq!(
            formula("all x, y P(x, y)").unwrap(),
            All(
                indexset!["x".into(), "y".into()],
                Box::new(Predicate(
                    "P".into(),
                    vec![Var("x".into()), Var("y".into())]
                ))
            )
        );
        assert_eq!(
            formula("ex x P(x)").unwrap(),
            Exists(
                indexset!["x".into()],
                Box::new(Predicate("P".into(), vec![Var("x".into())]))
            )
        );
        assert_eq!(
            formula("ex x, y P(x, y)").unwrap(),
            Exists(
                indexset!["x".into(), "y".into()],
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
            formula("P implies Q implies R").unwrap(),
            Implies(
                Box::new(formula("P").unwrap()),
                Box::new(Implies(
                    Box::new(formula("Q").unwrap()),
                    Box::new(formula("R").unwrap())
                ))
            )
        );
    }

    #[test]
    fn test_parse_pformula_precedence() {
        use PFormula::*;
        assert_eq!(formula("not P and Q or R implies S").unwrap(), {
            let p = formula("P").unwrap();
            let q = formula("Q").unwrap();
            let r = formula("R").unwrap();
            let s = formula("S").unwrap();
            let np = Not(Box::new(p));
            let np_and_q = And(vec![np, q]);
            let npq_or_r = Or(vec![np_and_q, r]);
            Implies(Box::new(npq_or_r), Box::new(s))
        });
    }

    #[test]
    fn test_parse_pformula_vec() {
        use PFormula::*;
        let fml = formula("P and Q and R and S").unwrap();
        assert_eq!(
            fml,
            And(vec![
                formula("P").unwrap(),
                formula("Q").unwrap(),
                formula("R").unwrap(),
                formula("S").unwrap(),
            ])
        );
        let fml = formula("P or Q or R or S").unwrap();
        assert_eq!(
            fml,
            Or(vec![
                formula("P").unwrap(),
                formula("Q").unwrap(),
                formula("R").unwrap(),
                formula("S").unwrap(),
            ])
        );
        let fml = formula("P and Q and (R or S or (T and U and V))").unwrap();
        assert_eq!(
            fml,
            And(vec![
                formula("P").unwrap(),
                formula("Q").unwrap(),
                Or(vec![
                    formula("R").unwrap(),
                    formula("S").unwrap(),
                    And(vec![
                        formula("T").unwrap(),
                        formula("U").unwrap(),
                        formula("V").unwrap(),
                    ]),
                ]),
            ])
        );
        let fml = formula("all x, y all z, u ex v ex w all h P").unwrap();
        assert_eq!(
            fml,
            All(
                indexset!["x".into(), "y".into(), "z".into(), "u".into()],
                Box::new(Exists(
                    indexset!["v".into(), "w".into()],
                    Box::new(All(indexset!["h".into()], Box::new(formula("P").unwrap())))
                ))
            )
        );
        let fml = formula("true and P and true and Q and true").unwrap();
        assert_eq!(
            fml,
            And(vec![formula("P").unwrap(), formula("Q").unwrap(),])
        );
        let fml = formula("false or P or false or Q or false").unwrap();
        assert_eq!(fml, Or(vec![formula("P").unwrap(), formula("Q").unwrap()]));
        let fml = formula("true and P").unwrap();
        assert_eq!(fml, formula("P").unwrap());
        let fml = formula("P and true").unwrap();
        assert_eq!(fml, formula("P").unwrap());
        let fml = formula("false or P").unwrap();
        assert_eq!(fml, formula("P").unwrap());
        let fml = formula("P or false").unwrap();
        assert_eq!(fml, formula("P").unwrap());
        let fml =
            formula("all x, y, z, x, y, z all x, y, z ex w, v, u ex u, v, w, w, v, u P").unwrap();
        assert_eq!(fml, formula("all x, y, z ex u, v, w P").unwrap());
    }

    #[test]
    fn test_parse() {
        let l = vec![
            (" \t \n \r P \t \n \r and \t \n \r Q \t \n \r ", "P ∧ Q"),
            ("Ｐ０", "P0"),
            ("(((P) and ((Q))))", "P ∧ Q"),
        ];
        for pair in l {
            let (s, expected) = pair;
            let (fml, entities) = parse(s).unwrap();
            assert_eq!(fml.display(&entities).to_string(), expected);
        }
    }

    #[test]
    fn test_check() {
        assert!(parse("P and P").is_ok());
        assert!(parse("P and P(x)").is_err_and(|e| { matches!(e, ParseError::PredicateArity) }));
        assert!(
            parse("P(x) and P(x,y)").is_err_and(|e| { matches!(e, ParseError::PredicateArity) })
        );
        assert!(parse("P(f(x), f(x)) and P(f(x), f(x))").is_ok());
        assert!(parse("P(f(x), f(x,y))").is_err_and(|e| { matches!(e, ParseError::FunctionArity) }));
        assert!(parse("P(f(x)) and P(f(x,y))")
            .is_err_and(|e| { matches!(e, ParseError::FunctionArity) }));
        assert!(parse("all x,y P(f(x,y))").is_ok());
        assert!(parse("(all Q,g P(f(Q,g))) and Q and P(g(x))").is_ok());
        assert!(parse("all f P(f(x,y))").is_err_and(|e| { matches!(e, ParseError::BddFunction) }));
        assert!(parse("all P P(f(x,y))").is_err_and(|e| { matches!(e, ParseError::BddPredicate) }));
        assert!(parse("all x ex z all x,y P(x,y,z)").is_ok());
    }

    #[test]
    fn test_universal_quantify() {
        let mut entities = EntitiesInfo::new();

        let fml = formula("all x,y P(f(x,y))")
            .unwrap()
            .into_formula_rec(&mut entities);
        assert_eq!(fml.clone().universal_quantify(), fml);

        let fml1 = formula("P(f(x,y))")
            .unwrap()
            .into_formula_rec(&mut entities);
        let Formula::All(vs1, p1) = fml1.universal_quantify() else {
            unreachable!()
        };
        let Formula::All(vs, p) = fml.clone().universal_quantify() else {
            unreachable!()
        };
        assert_eq!(
            vs1.iter().collect::<HashSet<_>>(),
            vs.iter().collect::<HashSet<_>>()
        );
        assert_eq!(p1, p);

        let fml2 = formula("all y P(f(x,y))")
            .unwrap()
            .into_formula_rec(&mut entities);
        assert_eq!(fml2.universal_quantify(), fml);
    }

    #[test]
    fn test_parse_tptp() {
        let s = "
% Comments : 
%--------------------------------------------------------------------------
fof(axiom1,axiom,(
s)).

fof(axiom2,axiom,(
( ~(( t => r) ) => p) )).

fof(con,conjecture,(
( ~(( ( p => q)  & ( t => r)  )) => ( ~(~(p)) & ( s & s ) )) 
)).

%--------------------------------------------------------------------------
";
        assert_eq!(
            from_tptp(s),
            "((s)) -> (((( ~(( t => r) ) => p) )) -> ((( ~(( ( p => q)  & ( t => r)  )) => ( ~(~(p)) & ( s & s ) )) )))"
        )
    }
}
