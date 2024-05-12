use crate::formula::{Formula, Term};
use crate::naming::Names;
use indexmap::IndexSet;
use itertools::Itertools;
use maplit::{hashmap, hashset};
use peg::{error, str::LineCol};
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::mem;
use thiserror::Error;
use unicode_normalization::UnicodeNormalization;

#[derive(Error, Debug)]
pub enum Error {
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
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum PTerm {
    Var(String),
    Func(String, Vec<PTerm>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PFormula {
    Pred(String, Vec<PTerm>),
    Not(Box<PFormula>),
    And(Vec<PFormula>),
    Or(Vec<PFormula>),
    Implies(Box<PFormula>, Box<PFormula>),
    All(IndexSet<String>, Box<PFormula>),
    Exists(IndexSet<String>, Box<PFormula>),
}

static P_TRUE: PFormula = PFormula::And(vec![]);
static P_FALSE: PFormula = PFormula::Or(vec![]);

pub fn parse(s: &str) -> Result<(Formula, Names), Error> {
    // Normalize the string.
    let s = s.nfkc().collect::<String>().trim().to_string();
    // Replace all whitespaces with a single space.
    let s = Regex::new(r"\s").unwrap().replace_all(&s, " ");
    // Check if the number of left and right parentheses are equal.
    let lp = s.chars().filter(|&c| c == '(').count();
    let rp = s.chars().filter(|&c| c == ')').count();
    if lp != rp {
        return Err(Error::Parentheses { lp, rp });
    }
    let pfml = parser::formula(&s).map_err(|e| Error::Core { s: s.into(), e })?;
    let mut names = Names::new();
    let mut fml = pfml.into_formula(&mut names);
    // Modify the formula.
    fml.flatten();
    fml.make_unique();
    fml.rename_bdd_vars1(&mut names, &mut hashset!(), &mut hashmap!());
    fml.rename_bdd_vars2(&mut names);
    fml.replace_free_vars_with_funcs(&mut hashset!());
    Ok((fml, names))
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
    pub(super) rule term() -> PTerm = quiet!{
        f:$function_name() _ "(" _ ts:(term() ++ (_ "," _)) _ ")" { Func(f.to_string(), ts) } /
        v:$var() { Var(v.to_string()) } /
        "(" t:term() ")" { t }
    } / expected!("term")

    rule predicate() -> PFormula =
        p_true() { P_TRUE.clone() } /
        p_false() { P_FALSE.clone() } /
        p:$predicate_name() _ "(" _ ts:(term() ++ (_ "," _)) _ ")" { Pred(p.to_string(), ts) } /
        p:$predicate_name() { Pred(p.to_string(), vec![]) }

    /// Parse a formula.
    ///
    /// All infix operators are right-associative.
    ///
    /// The precedence of operators is as follows: not, all, exists > and > or > implies > iff.
    pub(super) rule formula() -> PFormula = precedence!{
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
    fn into_term(self, names: &mut Names) -> Term {
        match self {
            Self::Var(name) => Term::Var(names.get_id(name)),
            Self::Func(name, pterms) => Term::Func(
                names.get_id(name),
                pterms
                    .into_iter()
                    .map(|pterm| pterm.into_term(names))
                    .collect(),
            ),
        }
    }
}

impl PFormula {
    fn into_formula(self, names: &mut Names) -> Formula {
        match self {
            Self::Pred(name, pterms) => Formula::Pred(
                names.get_id(name),
                pterms
                    .into_iter()
                    .map(|pterm| pterm.into_term(names))
                    .collect(),
            ),
            Self::Not(p) => Formula::Not(Box::new(p.into_formula(names))),
            Self::And(l) => Formula::And(l.into_iter().map(|p| p.into_formula(names)).collect()),
            Self::Or(l) => Formula::Or(l.into_iter().map(|p| p.into_formula(names)).collect()),
            Self::Implies(p, q) => Formula::Implies(
                Box::new(p.into_formula(names)),
                Box::new(q.into_formula(names)),
            ),
            Self::All(vs, p) => Formula::All(
                vs.into_iter().map(|name| names.get_id(name)).collect(),
                Box::new(p.into_formula(names)),
            ),
            Self::Exists(vs, p) => Formula::Exists(
                vs.into_iter().map(|name| names.get_id(name)).collect(),
                Box::new(p.into_formula(names)),
            ),
        }
    }
}

impl Term {
    /// Collects function IDs in the term.
    fn collect_func(&self, ids: &mut HashSet<usize>) {
        self.visit(&mut |t| {
            let Self::Func(id, _) = t else { return };
            ids.insert(*id);
        });
    }
}

impl Formula {
    /// Flattens the formula.
    ///
    /// Converts `(P ∧ Q) ∧ (R ∧ S)` to `P ∧ Q ∧ R ∧ S`.
    fn flatten(&mut self) {
        use Formula::*;
        match self {
            And(ps) => {
                let mut new_ps = vec![];
                while let Some(mut p) = ps.pop() {
                    p.flatten();
                    if let And(qs) = p {
                        new_ps.extend(qs);
                    } else {
                        new_ps.push(p);
                    }
                }
                *ps = new_ps
            }
            Or(ps) => {
                let mut new_ps = vec![];
                while let Some(mut p) = ps.pop() {
                    p.flatten();
                    if let Or(qs) = p {
                        new_ps.extend(qs);
                    } else {
                        new_ps.push(p);
                    }
                }
                *ps = new_ps
            }
            All(vs, p) => {
                p.flatten();
                match p.as_mut() {
                    All(ws, q) => {
                        vs.append(ws);
                        *p = mem::take(q);
                    }
                    _ => {}
                }
            }
            Exists(vs, p) => {
                p.flatten();
                match p.as_mut() {
                    Exists(ws, q) => {
                        vs.append(ws);
                        *p = mem::take(q);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// Makes ∧, ∨ and bounded variables unique.
    fn make_unique(&mut self) {
        use Formula::*;
        self.visit_mut(&mut |p| {
            match p {
                And(ps) | Or(ps) => {
                    *ps = ps.iter().unique().cloned().collect();
                    // if ps is a singleton, replace p with the element
                    if ps.len() == 1 {
                        *p = ps.pop().unwrap();
                    }
                }
                All(vs, _) | Exists(vs, _) => {
                    *vs = vs.iter().unique().cloned().collect();
                }
                _ => {}
            }
        });
    }

    /// Renames the bounded variables to avoid name conflicts.
    ///
    /// Converts `∀x (P(x) ∧ ∀x Q(x))` to `∀x (P(x) ∧ ∀x' Q(x'))`
    // TODO: 2024/05/12 apply_mutは使わない方がいいかも：all x P(x) ∧ all x Q(x) が all x P(x) ∧ all x' Q(x') になる
    fn rename_bdd_vars1(
        &mut self,
        names: &mut Names,
        bdd_vars: &mut HashSet<usize>,
        map: &mut HashMap<usize, Term>,
    ) {
        self.visit_mut(&mut |p| match p {
            Self::Pred(_, ts) => {
                for t in ts {
                    t.subst_map(map);
                }
            }
            Self::All(vs, _) | Self::Exists(vs, _) => {
                for v in vs {
                    if bdd_vars.contains(v) {
                        let new_v = names.get_fresh_id(names.get_name(*v));
                        map.insert(*v, Term::Var(new_v));
                        *v = new_v;
                    } else {
                        bdd_vars.insert(*v);
                    }
                }
            }
            _ => {}
        });
    }

    /// Collects function IDs in the formula.
    fn collect_func(&self) -> HashSet<usize> {
        let mut ids = hashset!();
        self.visit_terms(&mut |t| t.collect_func(&mut ids));
        ids
    }

    /// Collects predicate IDs in the formula.
    fn collect_pred(&self) -> HashSet<usize> {
        let mut ids = hashset!();
        self.visit(&mut |p| {
            let Self::Pred(id, _) = p else { return };
            ids.insert(*id);
        });
        ids
    }

    /// Renames the bounded variables to avoid using the same name as functions or predicates.
    ///
    /// Converts `∀P P(P)` to `∀P' P(P')`
    fn rename_bdd_vars2(&mut self, names: &mut Names) {
        let funcs = self.collect_func();
        let preds = self.collect_pred();
        self.visit_mut(&mut |p| {
            if let Self::All(vs, p) | Self::Exists(vs, p) = p {
                for v in vs {
                    if funcs.contains(v) || preds.contains(v) {
                        let new_v = names.get_fresh_id(names.get_name(*v));
                        p.subst(*v, &Term::Var(new_v));
                        *v = new_v;
                    }
                }
            }
        });
    }

    /// Substitutes free variables with functions with the same ID.
    ///
    /// Converts `P(x) ∧ ∀y Q(y)` to `P(x()) ∧ ∀y Q(y)`
    fn replace_free_vars_with_funcs(&mut self, bdd_vars: &HashSet<usize>) {
        use Formula::*;
        match self {
            Pred(_, ts) => {
                for t in ts {
                    t.visit_mut(&mut |v| {
                        let Term::Var(id) = v else { return };
                        if bdd_vars.contains(id) {
                            return;
                        }
                        *v = Term::Func(*id, vec![]);
                    });
                }
            }
            Not(p) => p.replace_free_vars_with_funcs(bdd_vars),
            And(l) | Or(l) => {
                for p in l {
                    p.replace_free_vars_with_funcs(bdd_vars);
                }
            }
            Implies(p, q) => {
                p.replace_free_vars_with_funcs(bdd_vars);
                q.replace_free_vars_with_funcs(bdd_vars);
            }
            All(vs, p) | Exists(vs, p) => {
                let mut bdd_vars = bdd_vars.clone();
                bdd_vars.extend(vs.iter().cloned());
                p.replace_free_vars_with_funcs(&bdd_vars);
            }
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
            Func("f".into(), vec![Var("x".into())])
        );
        assert_eq!(
            term("f(x, g(y), z)").unwrap(),
            Func(
                "f".into(),
                vec![
                    Var("x".into()),
                    Func("g".into(), vec![Var("y".into())]),
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
        assert_eq!(formula("P").unwrap(), Pred("P".into(), vec![]));
        assert_eq!(
            formula("P(x)").unwrap(),
            Pred("P".into(), vec![Var("x".into())])
        );
        assert_eq!(
            formula("P(x, g(y), z)").unwrap(),
            Pred(
                "P".into(),
                vec![
                    Var("x".into()),
                    Func("g".into(), vec![Var("y".into())]),
                    Var("z".into())
                ]
            )
        );
        assert_eq!(
            formula("not P").unwrap(),
            Not(Box::new(Pred("P".into(), vec![])))
        );
        assert_eq!(
            formula("P and Q").unwrap(),
            And(vec![Pred("P".into(), vec![]), Pred("Q".into(), vec![])])
        );
        assert_eq!(
            formula("P or Q").unwrap(),
            Or(vec![Pred("P".into(), vec![]), Pred("Q".into(), vec![])])
        );
        assert_eq!(
            formula("P implies Q").unwrap(),
            Implies(
                Box::new(Pred("P".into(), vec![])),
                Box::new(Pred("Q".into(), vec![]))
            )
        );
        assert_eq!(
            formula("P iff Q").unwrap(),
            And(vec![
                Implies(
                    Box::new(Pred("P".into(), vec![])),
                    Box::new(Pred("Q".into(), vec![]))
                ),
                Implies(
                    Box::new(Pred("Q".into(), vec![])),
                    Box::new(Pred("P".into(), vec![]))
                )
            ])
        );
        assert_eq!(
            formula("all x P(x)").unwrap(),
            All(
                indexset!["x".into()],
                Box::new(Pred("P".into(), vec![Var("x".into())]))
            )
        );
        assert_eq!(
            formula("all x, y P(x, y)").unwrap(),
            All(
                indexset!["x".into(), "y".into()],
                Box::new(Pred("P".into(), vec![Var("x".into()), Var("y".into())]))
            )
        );
        assert_eq!(
            formula("ex x P(x)").unwrap(),
            Exists(
                indexset!["x".into()],
                Box::new(Pred("P".into(), vec![Var("x".into())]))
            )
        );
        assert_eq!(
            formula("ex x, y P(x, y)").unwrap(),
            Exists(
                indexset!["x".into(), "y".into()],
                Box::new(Pred("P".into(), vec![Var("x".into()), Var("y".into())]))
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
            let (fml, names) = parse(s).unwrap();
            assert_eq!(fml.display(&names).to_string(), expected);
        }
    }

    #[test]
    fn test_adjust_bdd_vars() {
        fn test(s: &str, expected: &str) {
            let (mut fml, mut names) = parse(s).unwrap();
            let mut bdd_vars = hashset![];
            let mut new_bdd_vars = hashmap![];
            fml.rename_bdd_vars1(&mut names, &mut bdd_vars, &mut new_bdd_vars);
            assert_eq!(fml.display(&names).to_string(), expected);
        }
        test("∀x P(x)", "∀xP(x)");
        test("∀x,y P(x,y)", "∀x,yP(x,y)");
        test("∀x,y P(x,y) ∧ ∀x,y Q(x,y)", "∀x,yP(x,y) ∧ ∀x',y'Q(x',y')");
        test("∀x∃x∀x∃x P(x)", "∀x∃x'∀x''∃x'''P(x''')");
        test("∀x (P(x) ∧ ∀x Q(x))", "∀x(P(x) ∧ ∀x'Q(x'))");
    }

    #[test]
    fn test_check() {
        // assert!(parse("(all Q,g P(f(Q,g))) and Q and P(g(x))").is_ok());
        // assert!(parse("all f P(f(x,y))").is_err_and(|e| { matches!(e, ParseError::BddFunction) }));
        // assert!(parse("all P P(f(x,y))").is_err_and(|e| { matches!(e, ParseError::BddPredicate) }));
        // assert!(parse("all x ex z all x,y P(x,y,z)").is_ok());
    }

    // fn test_universal_quantify() {
    //     let fml = formula("all x,y P(f(x,y))")
    //         .unwrap()
    //         .into_formula(&mut names);
    //     assert_eq!(fml.clone().universal_quantify(), fml);

    //     let fml1 = formula("P(f(x,y))").unwrap().into_formula(&mut names);
    //     let Formula::All(vs1, p1) = fml1.universal_quantify() else {
    //         unreachable!()
    //     };
    //     let Formula::All(vs, p) = fml.clone().universal_quantify() else {
    //         unreachable!()
    //     };
    //     assert_eq!(
    //         vs1.iter().collect::<HashSet<_>>(),
    //         vs.iter().collect::<HashSet<_>>()
    //     );
    //     assert_eq!(p1, p);
    //     let fml2 = formula("all y P(f(x,y))").unwrap().into_formula(&mut names);
    //     assert_eq!(fml2.universal_quantify(), fml);
    // }
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
