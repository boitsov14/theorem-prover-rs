use crate::lang::{Formula, Sequent, Term};
use crate::name::Names;
use itertools::Itertools;
use maplit::{hashmap, hashset};
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::mem;
use thiserror::Error;
use unicode_normalization::UnicodeNormalization;

/// Parse error.
#[derive(Error, Debug)]
pub enum Error {
    /// Mismatched parentheses.
    #[error("Found {lp} left parentheses and {rp} right parentheses.")]
    Parentheses { lp: usize, rp: usize },
    /// Peg parser error.
    #[error("
 | 
 | {s}
 | {}^___
 | 
 = expected {}", " ".repeat(e.location.column - 1), e.expected)]
    Peg {
        s: String,
        e: peg::error::ParseError<peg::str::LineCol>,
    },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum PTerm {
    Var(String),
    Func(String, Vec<PTerm>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PFormula {
    True,
    False,
    Pred(String, Vec<PTerm>),
    Not(Box<PFormula>),
    And(Box<PFormula>, Box<PFormula>),
    Or(Box<PFormula>, Box<PFormula>),
    To(Box<PFormula>, Box<PFormula>),
    Iff(Box<PFormula>, Box<PFormula>),
    All(String, Box<PFormula>),
    Ex(String, Box<PFormula>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PSequent {
    ant: Vec<PFormula>,
    suc: Vec<PFormula>,
}

/// Parses a term.
pub(super) fn parse_term(s: &str, names: &mut Names) -> Result<Term, Error> {
    let s = modify_string(s);
    check_parentheses(&s)?;
    let pterm = parser::term(&s).map_err(|e| Error::Peg { s, e })?;
    Ok(pterm.into_term(names))
}

/// Parses a formula.
pub(super) fn parse_formula(
    s: &str,
    names: &mut Names,
    modify_formula: bool,
) -> Result<Formula, Error> {
    let s = modify_string(s);
    check_parentheses(&s)?;
    let pfml = parser::formula(&s).map_err(|e| Error::Peg { s, e })?;
    let mut fml = pfml.into_formula(names);
    if modify_formula {
        fml.modify(names);
    }
    Ok(fml)
}

/// Parses a sequent.
pub fn parse_sequent(
    s: &str,
    names: &mut Names,
    modify_formula: bool,
    tptp: bool,
) -> Result<Sequent, Error> {
    let s = if tptp { modify_tptp(s) } else { s.to_string() };
    let s = modify_string(&s);
    check_parentheses(&s)?;
    let pseq = parser::sequent(&s).map_err(|e| Error::Peg { s, e })?;
    let mut seq = pseq.into_sequent(names);
    if modify_formula {
        seq.visit_formulas_mut(|p| p.modify(names));
        seq.unique();
    }
    Ok(seq)
}

/// Modifies the string.
fn modify_string(s: &str) -> String {
    // Normalize the string.
    let s = s.nfkc().collect::<String>().trim().to_string();
    // Replace all whitespaces with a single space.
    Regex::new(r"\s+").unwrap().replace_all(&s, " ").to_string()
}

/// Checks if the number of left and right parentheses are equal.
fn check_parentheses(s: &str) -> Result<(), Error> {
    let lp = s.chars().filter(|&c| c == '(').count();
    let rp = s.chars().filter(|&c| c == ')').count();
    if lp == rp {
        Ok(())
    } else {
        Err(Error::Parentheses { lp, rp })
    }
}

/// Modifies the TPTP format.
fn modify_tptp(s: &str) -> String {
    let s = s
        .lines()
        .filter(|line| !line.trim_start().starts_with('%'))
        .collect::<String>();

    let axioms = Regex::new(r"fof\(([^,]+),axiom,(.+?)\)\.")
        .unwrap()
        .captures_iter(&s)
        .map(|cap| cap[2].trim().to_string())
        .join(", ");

    let conjecture = Regex::new(r"fof\(([^,]+),conjecture,(.+?)\)\.")
        .unwrap()
        .captures(&s)
        .unwrap()[2]
        .trim()
        .to_string();

    format!("{axioms} ⊢ {conjecture}").replace('$', "")
}

peg::parser!( grammar parser() for str {
    use PFormula::*;
    use PTerm::*;

    /// Parses a term.
    pub(super) rule term() -> PTerm = quiet!{
        f:$func_id() _ "(" _ ts:(term() ++ (_ "," _)) _ ")" { Func(f.to_string(), ts) } /
        v:$var_id() { Var(v.to_string()) } /
        "(" t:term() ")" { t }
    } / expected!("term")

    rule predicate() -> PFormula =
        p_true() { True.clone() } /
        p_false() { False.clone() } /
        p:$pred_id() _ "(" _ ts:(term() ++ (_ "," _)) _ ")" { Pred(p.to_string(), ts) } /
        p:$pred_id() { Pred(p.to_string(), vec![]) }

    /// Parses a formula.
    ///
    /// All infix operators are right-associative.
    ///
    /// The precedence of operators is as follows: ¬, ∀, ∃ > ∧ > ∨ > → > ↔.
    pub(super) rule formula() -> PFormula = precedence!{
        p:@ _ iff() _ q:(@) { Iff(Box::new(p), Box::new(q)) }
        --
        p:@ _ to() _ q:(@) { To(Box::new(p), Box::new(q)) }
        --
        p:@ _ or() _ q:(@) { Or(Box::new(p), Box::new(q)) }
        --
        p:@ _ and() _ q:(@) { And(Box::new(p), Box::new(q)) }
        --
        not() _ p:@ { Not(Box::new(p)) }
        all() _ vs:($bdd_var_id() ++ (_ "," _)) _ p:@ { vs.iter().rev().fold(p, |p, &s| All(s.into(), Box::new(p))) }
        ex() _ vs:($bdd_var_id() ++ (_ "," _)) _ p:@ { vs.iter().rev().fold(p, |p, &s| Ex(s.into(), Box::new(p))) }
        --
        p:predicate() { p }
        "(" _ p:formula() _ ")" { p }
    } / expected!("formula")

    /// Parses a sequent.
    pub(super) rule sequent() -> PSequent =
        ant:(formula() ** (_ "," _)) _ turnstile() _ suc:(formula() ** (_ "," _)) { PSequent { ant, suc } } /
        p:formula() { PSequent { ant: vec![], suc: vec![p] } } /
        expected!("sequent")

    rule alpha() = [ 'a'..='z' | 'A'..='Z' ]
    rule digit() = [ '0'..='9' | '_' | '\'' ]
    rule id() = alpha() (alpha() / digit())*
    rule var_id() = id()
    rule bdd_var_id() = alpha() digit()*
    rule func_id() = id()
    rule pred_id() = quiet!{ id() } / expected!("predicate")
    rule p_true() = quiet!{ "⊤" / "true" / r"\top" }
    rule p_false() = quiet!{ "⊥" / "⟂" / "false" / r"\bot" }
    rule not() = quiet!{ "¬" / "~" / "not" / r"\lnot" / r"\neg" } / expected!(r#""¬""#)
    rule and() = quiet!{ "∧" / r"/\" / "&" / "and" / r"\land" / r"\wedge" } / expected!(r#""∧""#)
    rule or() = quiet!{ "∨" / r"\/" / "|" / "or" / r"\lor" / r"\vee" } / expected!(r#""∨""#)
    rule to() = quiet!{ "→" / "->" / "=>" / "to" / r"\rightarrow" / r"\to" } / expected!(r#""→""#)
    rule iff() = quiet!{ "↔" / "<->" / "<=>" / "iff" / r"\leftrightarrow" } / expected!(r#""↔""#)
    rule all() = quiet!{ "∀" / "!" / "all" / r"\forall" } / expected!(r#""∀""#)
    rule ex() = quiet!{ "∃" / "?" / "ex" / r"\exists" } / expected!(r#""∃""#)
    rule turnstile() = quiet!{ "⊢" / "|-" / "├" / "┣" / r"\vdash" } / expected!(r#""⊢""#)
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
            Self::True => Formula::And(vec![]),
            Self::False => Formula::Or(vec![]),
            Self::Pred(name, pterms) => Formula::Pred(
                names.get_id(name),
                pterms
                    .into_iter()
                    .map(|pterm| pterm.into_term(names))
                    .collect(),
            ),
            Self::Not(p) => Formula::Not(Box::new(p.into_formula(names))),
            Self::And(p, q) => Formula::And(vec![p.into_formula(names), q.into_formula(names)]),
            Self::Or(p, q) => Formula::Or(vec![p.into_formula(names), q.into_formula(names)]),
            Self::To(p, q) => Formula::To(
                Box::new(p.into_formula(names)),
                Box::new(q.into_formula(names)),
            ),
            Self::Iff(p, q) => Formula::Iff(
                Box::new(p.into_formula(names)),
                Box::new(q.into_formula(names)),
            ),
            Self::All(s, p) => Formula::All(vec![names.get_id(s)], Box::new(p.into_formula(names))),
            Self::Ex(s, p) => Formula::Ex(vec![names.get_id(s)], Box::new(p.into_formula(names))),
        }
    }
}

impl PSequent {
    fn into_sequent(self, names: &mut Names) -> Sequent {
        Sequent {
            ant: self
                .ant
                .into_iter()
                .map(|p| p.into_formula(names))
                .collect(),
            suc: self
                .suc
                .into_iter()
                .map(|p| p.into_formula(names))
                .collect(),
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
    /// Modifies the formula.
    fn modify(&mut self, names: &mut Names) {
        self.flatten();
        self.unique();
        self.rename_nested_bdd_vars(names, &hashmap!());
        self.rename_bdd_vars(names);
        self.subst_free_vars_with_constants(&hashset!());
    }

    /// Flattens the formula.
    /// # Examples
    /// Converts `(P ∧ Q) ∧ (R ∧ S)` to `P ∧ Q ∧ R ∧ S`.
    ///
    /// Converts `(P ∨ Q) ∨ (R ∨ S)` to `P ∨ Q ∨ R ∨ S`.
    ///
    /// Converts `∀x(∀y(∀zP(x,y,z)))` to `∀x,y,zP(x,y,z)`.
    ///
    /// Converts `∃x(∃y(∃zP(x,y,z)))` to `∃x,y,zP(x,y,z)`.
    fn flatten(&mut self) {
        use Formula::*;
        self.visit_mut(&mut |p| match p {
            And(ps) => {
                let mut new_ps = vec![];
                for p in ps.drain(..) {
                    if let And(qs) = p {
                        new_ps.extend(qs);
                    } else {
                        new_ps.push(p);
                    }
                }
                *ps = new_ps;
            }
            Or(ps) => {
                let mut new_ps = vec![];
                for p in ps.drain(..) {
                    if let Or(qs) = p {
                        new_ps.extend(qs);
                    } else {
                        new_ps.push(p);
                    }
                }
                *ps = new_ps;
            }
            All(vs, p) => {
                let All(ws, q) = p.as_mut() else { return };
                vs.append(ws);
                *p = mem::take(q);
            }
            Ex(vs, p) => {
                let Ex(ws, q) = p.as_mut() else { return };
                vs.append(ws);
                *p = mem::take(q);
            }
            _ => {}
        });
    }

    /// Makes ∧, ∨ and bounded variables unique.
    /// # Examples
    /// Converts `P ∧ P` to `P`.
    ///
    /// Converts `P ∨ P` to `P`.
    ///
    /// Converts `∀x,xP(x)` to `∀xP(x)`.
    ///
    /// Converts `∃x,xP(x)` to `∃xP(x)`.
    fn unique(&mut self) {
        use Formula::*;
        self.visit_mut(&mut |p| {
            match p {
                And(ps) | Or(ps) => {
                    let mut new_ps = vec![];
                    for p in ps.drain(..) {
                        if !new_ps.contains(&p) {
                            new_ps.push(p);
                        }
                    }
                    *ps = new_ps;
                    // if ps is a singleton, replace p with the element
                    if ps.len() == 1 {
                        *p = ps.pop().unwrap();
                    }
                }
                All(vs, _) | Ex(vs, _) => {
                    let mut new_vs = vec![];
                    for v in vs.drain(..) {
                        if !new_vs.contains(&v) {
                            new_vs.push(v);
                        }
                    }
                    *vs = new_vs;
                }
                _ => {}
            }
        });
    }

    /// Renames the nested bounded variables to avoid ID conflicts.
    /// # Examples
    /// Converts `∀x(P(x) ∧ ∀xQ(x))` to `∀x(P(x) ∧ ∀x'Q(x'))`
    fn rename_nested_bdd_vars(&mut self, names: &mut Names, map: &HashMap<usize, Term>) {
        use Formula::*;
        match self {
            Pred(_, ts) => {
                for t in ts {
                    t.subst_map(map);
                }
            }
            All(vs, p) | Ex(vs, p) => {
                let mut map = map.clone();
                for v in vs {
                    if map.contains_key(v) {
                        let new_v = names.gen_fresh_id(*v);
                        map.insert(*v, Term::Var(new_v));
                        *v = new_v;
                    } else {
                        map.insert(*v, Term::Var(*v));
                    }
                }
                p.rename_nested_bdd_vars(names, &map);
            }
            _ => {
                self.visit_children_mut(|p| p.rename_nested_bdd_vars(names, map));
            }
        }
    }

    /// Collects function IDs in the formula.
    fn collect_func(&self) -> HashSet<usize> {
        let mut ids = hashset!();
        self.visit_terms(|t| t.collect_func(&mut ids));
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

    /// Renames the bounded variables to avoid using the same ID as functions or predicates.
    ///
    /// This is optional to avoid misunderstandings.
    /// # Examples
    /// Converts `∀PP(P)` to `∀P'P(P')`
    ///
    /// Converts `∀fP(f(f))` to `∀f'P(f(f'))`
    fn rename_bdd_vars(&mut self, names: &mut Names) {
        let funcs = self.collect_func();
        let preds = self.collect_pred();
        self.visit_mut(&mut |p| {
            if let Self::All(vs, p) | Self::Ex(vs, p) = p {
                for v in vs {
                    if funcs.contains(v) || preds.contains(v) {
                        let new_v = names.gen_fresh_id(*v);
                        p.subst(*v, &Term::Var(new_v));
                        *v = new_v;
                    }
                }
            }
        });
    }

    /// Substitutes free variables with constants(0-ary functions) of the same ID.
    /// # Examples
    /// Converts `P(x) ∧ ∀yQ(y)` to `P(x()) ∧ ∀yQ(y)`
    fn subst_free_vars_with_constants(&mut self, bdd_vars: &HashSet<usize>) {
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
            All(vs, p) | Ex(vs, p) => {
                let mut bdd_vars = bdd_vars.clone();
                bdd_vars.extend(vs.iter().copied());
                p.subst_free_vars_with_constants(&bdd_vars);
            }
            _ => {
                self.visit_children_mut(|p| p.subst_free_vars_with_constants(bdd_vars));
            }
        }
    }
}

impl Sequent {
    /// Removes duplicate elements from `ant` and `suc`.
    fn unique(&mut self) {
        let mut new_ant = vec![];
        for p in self.ant.drain(..) {
            if !new_ant.contains(&p) {
                new_ant.push(p);
            }
        }
        self.ant = new_ant;
        let mut new_suc = vec![];
        for p in self.suc.drain(..) {
            if !new_suc.contains(&p) {
                new_suc.push(p);
            }
        }
        self.suc = new_suc;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::case;

    fn pterm(s: &str) -> PTerm {
        parser::term(s).unwrap()
    }
    fn pfml(s: &str) -> PFormula {
        parser::formula(s).unwrap()
    }
    fn pseq(s: &str) -> PSequent {
        parser::sequent(s).unwrap()
    }

    #[test]
    fn test_parse_pterm() {
        use PTerm::*;
        assert_eq!(pterm("x"), Var("x".into()));
        assert_eq!(pterm("f(x)"), Func("f".into(), vec![pterm("x")]));
        assert_eq!(
            pterm("f(x,g(y),z)"),
            Func("f".into(), vec![pterm("x"), pterm("g(y)"), pterm("z")])
        );
    }

    #[test]
    fn test_parse_pfml() {
        use PFormula::*;
        assert_eq!(pfml("⊤"), True);
        assert_eq!(pfml("⊥"), False);
        assert_eq!(pfml("P"), Pred("P".into(), vec![]));
        assert_eq!(pfml("P(x)"), Pred("P".into(), vec![pterm("x")]));
        assert_eq!(
            pfml("P(x,f(y),z)"),
            Pred("P".into(), vec![pterm("x"), pterm("f(y)"), pterm("z")])
        );
        assert_eq!(pfml("¬P"), Not(Box::new(pfml("P"))));
        assert_eq!(pfml("P ∧ Q"), And(Box::new(pfml("P")), Box::new(pfml("Q"))));
        assert_eq!(pfml("P ∨ Q"), Or(Box::new(pfml("P")), Box::new(pfml("Q"))));
        assert_eq!(pfml("P → Q"), To(Box::new(pfml("P")), Box::new(pfml("Q"))));
        assert_eq!(pfml("P ↔ Q"), Iff(Box::new(pfml("P")), Box::new(pfml("Q"))));
        assert_eq!(pfml("∀xP(x)"), All("x".into(), Box::new(pfml("P(x)"))));
        assert_eq!(
            pfml("∀x,yP(x,y)"),
            All(
                "x".into(),
                Box::new(All("y".into(), Box::new(pfml("P(x,y)"))))
            )
        );
        assert_eq!(
            pfml("∀x,y,zP(x,y,z)"),
            All(
                "x".into(),
                Box::new(All(
                    "y".into(),
                    Box::new(All("z".into(), Box::new(pfml("P(x,y,z)"))))
                ))
            )
        );
        assert_eq!(pfml("∃xP(x)"), Ex("x".into(), Box::new(pfml("P(x)"))));
        assert_eq!(
            pfml("∃x,yP(x,y)"),
            Ex(
                "x".into(),
                Box::new(Ex("y".into(), Box::new(pfml("P(x,y)"))))
            )
        );
        assert_eq!(
            pfml("∃x,y,zP(x,y,z)"),
            Ex(
                "x".into(),
                Box::new(Ex(
                    "y".into(),
                    Box::new(Ex("z".into(), Box::new(pfml("P(x,y,z)"))))
                ))
            )
        );
    }

    #[test]
    fn test_parse_pfml_assoc() {
        use PFormula::*;
        assert_eq!(
            pfml("P → Q → R"),
            To(
                Box::new(pfml("P")),
                Box::new(To(Box::new(pfml("Q")), Box::new(pfml("R"))))
            )
        );
    }

    #[test]
    fn test_parse_pfml_precedence() {
        use PFormula::*;
        assert_eq!(
            pfml("¬P ∧ Q ∨ R → S ↔ T"),
            Iff(
                Box::new(To(
                    Box::new(Or(
                        Box::new(And(Box::new(Not(Box::new(pfml("P")))), Box::new(pfml("Q")))),
                        Box::new(pfml("R"))
                    )),
                    Box::new(pfml("S"))
                )),
                Box::new(pfml("T"))
            )
        );
        assert_eq!(
            pfml("∀xP(x) → ∃yQ(y) → R"),
            To(
                Box::new(All("x".into(), Box::new(pfml("P(x)")))),
                Box::new(To(
                    Box::new(Ex("y".into(), Box::new(pfml("Q(y)")))),
                    Box::new(pfml("R"))
                ))
            )
        );
    }

    #[test]
    fn test_parse_pseq() {
        assert_eq!(
            pseq("P, Q, R ⊢ S, T, U"),
            PSequent {
                ant: vec![pfml("P"), pfml("Q"), pfml("R")],
                suc: vec![pfml("S"), pfml("T"), pfml("U")]
            }
        );
        assert_eq!(
            pseq("P, Q ⊢ R, S"),
            PSequent {
                ant: vec![pfml("P"), pfml("Q")],
                suc: vec![pfml("R"), pfml("S")]
            }
        );
        assert_eq!(
            pseq("P ⊢ Q"),
            PSequent {
                ant: vec![pfml("P")],
                suc: vec![pfml("Q")]
            }
        );
        assert_eq!(
            pseq("P ⊢"),
            PSequent {
                ant: vec![pfml("P")],
                suc: vec![]
            }
        );
        assert_eq!(
            pseq("⊢ P"),
            PSequent {
                ant: vec![],
                suc: vec![pfml("P")]
            }
        );
        assert_eq!(
            pseq("⊢"),
            PSequent {
                ant: vec![],
                suc: vec![]
            }
        );
        assert_eq!(
            pseq("P ∧ Q, R ∨ S, ∀xP(x) ⊢ ∃yQ(y), ¬R, ∃z∀wS(z,w)"),
            PSequent {
                ant: vec![pfml("P ∧ Q"), pfml("R ∨ S"), pfml("∀xP(x)")],
                suc: vec![pfml("∃yQ(y)"), pfml("¬R"), pfml("∃z∀wS(z,w)")]
            }
        );
        assert_eq!(
            pseq("P"),
            PSequent {
                ant: vec![],
                suc: vec![pfml("P")]
            }
        );
        assert_eq!(
            pseq("¬P ∧ Q ∨ R → S ↔ ∀x∃yP(x,y)"),
            PSequent {
                ant: vec![],
                suc: vec![pfml("¬P ∧ Q ∨ R → S ↔ ∀x∃yP(x,y)")]
            }
        );
    }

    #[test]
    fn test_nfkc() {
        let mut names = Names::default();
        let fml = parse_formula("Ｐ０", &mut names, false).unwrap();
        assert_eq!(fml.display(&names).to_string(), "P0");
    }

    #[case("\t\n\rP\t\n\r∧\t\n\rQ\t\n\r" => "P ∧ Q")]
    #[case("(((P)∧((Q))))" => "P ∧ Q")]
    fn test_parse_fml(s: &str) -> String {
        let mut names = Names::default();
        let fml = parse_formula(s, &mut names, false).unwrap();
        fml.display(&names).to_string()
    }

    #[test]
    fn test_flatten_and() {
        use Formula::*;
        let mut names = Names::default();
        let mut fml1 = parse_formula("P ∧ Q ∧ R ∧ S", &mut names, false).unwrap();
        let mut fml2 = parse_formula("((P ∧ Q) ∧ R) ∧ S", &mut names, false).unwrap();
        let mut fml3 = parse_formula("(P ∧ Q) ∧ (R ∧ S)", &mut names, false).unwrap();
        fml1.flatten();
        fml2.flatten();
        fml3.flatten();
        let expected = And(vec![
            parse_formula("P", &mut names, false).unwrap(),
            parse_formula("Q", &mut names, false).unwrap(),
            parse_formula("R", &mut names, false).unwrap(),
            parse_formula("S", &mut names, false).unwrap(),
        ]);
        assert_eq!(fml1, expected);
        assert_eq!(fml2, expected);
        assert_eq!(fml3, expected);
    }

    #[test]
    fn test_flatten_and_or() {
        use Formula::*;
        let mut names = Names::default();
        let mut fml =
            parse_formula("(P ∧ Q ∧ (R ∨ S ∨ (T ∧ U ∧ V))) → W", &mut names, false).unwrap();
        fml.flatten();
        assert_eq!(
            fml,
            To(
                Box::new(And(vec![
                    parse_formula("P", &mut names, false).unwrap(),
                    parse_formula("Q", &mut names, false).unwrap(),
                    Or(vec![
                        parse_formula("R", &mut names, false).unwrap(),
                        parse_formula("S", &mut names, false).unwrap(),
                        And(vec![
                            parse_formula("T", &mut names, false).unwrap(),
                            parse_formula("U", &mut names, false).unwrap(),
                            parse_formula("V", &mut names, false).unwrap(),
                        ]),
                    ]),
                ])),
                Box::new(parse_formula("W", &mut names, false).unwrap())
            )
        );
    }

    #[test]
    fn test_flatten_all() {
        use Formula::*;
        let mut names = Names::default();
        let mut fml = parse_formula("∀x,y∀z,u∀v,wP(x,y,z,u,v,w)", &mut names, false).unwrap();
        fml.flatten();
        assert_eq!(
            fml,
            All(
                vec![
                    names.get_id("x".into()),
                    names.get_id("y".into()),
                    names.get_id("z".into()),
                    names.get_id("u".into()),
                    names.get_id("v".into()),
                    names.get_id("w".into())
                ],
                Box::new(parse_formula("P(x,y,z,u,v,w)", &mut names, false).unwrap())
            )
        );
    }

    #[test]
    fn test_flatten_all_ex() {
        use Formula::*;
        let mut names = Names::default();
        let mut fml = parse_formula("∀x∀y∃z∃u∀v∀wP(x,y,z,u,v,w) → Q", &mut names, false).unwrap();
        fml.flatten();
        assert_eq!(
            fml,
            To(
                Box::new(All(
                    vec![names.get_id("x".into()), names.get_id("y".into()),],
                    Box::new(Ex(
                        vec![names.get_id("z".into()), names.get_id("u".into()),],
                        Box::new(All(
                            vec![names.get_id("v".into()), names.get_id("w".into()),],
                            Box::new(parse_formula("P(x,y,z,u,v,w)", &mut names, false).unwrap())
                        ))
                    ))
                )),
                Box::new(parse_formula("Q", &mut names, false).unwrap())
            )
        );
    }

    #[case("P ∧ P ∧ Q ∧ Q ∧ R ∧ R ∧ P ∧ Q ∧ R" => "P ∧ Q ∧ R")]
    #[case("⊤ ∧ P ∧ ⊤ ∧ Q ∧ ⊤" => "P ∧ Q")]
    #[case("⊥ ∨ Q ∨ ⊥ ∨ P ∨ ⊥" => "Q ∨ P")]
    #[case("(P ∧ ⊤ ∧ P ∧ ⊥ ∨ P ∧ P ∨ ⊤) → P" => "((P ∧ ⊥) ∨ P ∨ ⊤) → P")]
    #[case("∀x∀x∀y∀y∀z∀z∀x∀y∀zP(x,y,z)" => "∀x∀y∀zP(x,y,z)")]
    #[case("∀x∀x∃x∃x∀x∀xP(x,y) → Q" => "∀x∃x∀xP(x,y) → Q")]
    fn test_unique(s: &str) -> String {
        let mut names = Names::default();
        let mut fml = parse_formula(s, &mut names, false).unwrap();
        fml.flatten();
        fml.unique();
        fml.display(&names).to_string()
    }

    #[case("P ∧ P", "P")]
    #[case("P ∧ ⊤", "P")]
    #[case("Q ∨ ⊥", "Q")]
    fn test_unique_singleton(s: &str, name: &str) {
        let mut names = Names::default();
        let mut fml = parse_formula(s, &mut names, false).unwrap();
        fml.flatten();
        fml.unique();
        let pred = Formula::Pred(names.get_id(name.into()), vec![]);
        assert_eq!(fml, pred);
    }

    #[case("∀xP(x)" => "∀xP(x)")]
    #[case("∀x∀yP(x,y)" => "∀x∀yP(x,y)")]
    #[case("∀x∀yP(x,y) ∧ ∀x∀yQ(x,y)" => "∀x∀yP(x,y) ∧ ∀x∀yQ(x,y)")]
    #[case("∀x(P(x) → ∀xQ(x))" => "∀x(P(x) → ∀x'Q(x'))")]
    #[case("∀x(P(x) → ∀x(Q(x) → ∀xR(x)))" => "∀x(P(x) → ∀x'(Q(x') → ∀x''R(x'')))")]
    #[case("∀x(P(x) → ∀x(Q(x) → ∀x(R(x) → ∀xS(x))))" => "∀x(P(x) → ∀x'(Q(x') → ∀x''(R(x'') → ∀x'''S(x'''))))")]
    #[case("∀x∃x∀x∃xP(x)" => "∀x∃x'∀x''∃x'''P(x''')")]
    fn test_rename_nested_bdd_vars(s: &str) -> String {
        let mut names = Names::default();
        let mut fml = parse_formula(s, &mut names, false).unwrap();
        fml.flatten();
        fml.rename_nested_bdd_vars(&mut names, &hashmap!());
        fml.display(&names).to_string()
    }

    #[case("∀xP(x)" => "∀xP(x)")]
    #[case("∀PP(P)" => "∀P'P(P')")]
    #[case("∀fP(f(f))" => "∀f'P(f(f'))")]
    #[case("∀fP(f(f'(f''(f'''(f)))))" => "∀f''''P(f(f'(f''(f'''(f'''')))))")]
    fn test_rename_bdd_vars(s: &str) -> String {
        let mut names = Names::default();
        let mut fml = parse_formula(s, &mut names, false).unwrap();
        fml.rename_bdd_vars(&mut names);
        fml.display(&names).to_string()
    }

    #[test]
    fn test_subst_free_vars_with_constants() {
        use Formula::*;
        use Term::*;
        let mut names = Names::default();
        let mut fml = parse_formula("P(x) ∧ ∀yQ(y,f(z))", &mut names, false).unwrap();
        fml.subst_free_vars_with_constants(&hashset!());
        assert_eq!(
            fml,
            And(vec![
                Pred(
                    names.get_id("P".into()),
                    vec![Func(names.get_id("x".into()), vec![])]
                ),
                All(
                    vec![names.get_id("y".into())],
                    Box::new(Pred(
                        names.get_id("Q".into()),
                        vec![
                            Var(names.get_id("y".into())),
                            Func(
                                names.get_id("f".into()),
                                vec![Func(names.get_id("z".into()), vec![])]
                            )
                        ]
                    ))
                )
            ])
        );
    }

    #[case("P, P, P ⊢ P, P, P" => "P ⊢ P")]
    #[case("P, Q, P, Q ⊢ P, P, Q, Q" => "P, Q ⊢ P, Q")]
    fn test_unique_seq(s: &str) -> String {
        let mut names = Names::default();
        let mut seq = parse_sequent(s, &mut names, false, false).unwrap();
        seq.unique();
        seq.display(&names).to_string()
    }

    #[test]
    fn test_tptp_prop() {
        let s = "
% Comments : 
%--------------------------------------------------------------------------
fof(axiom1,axiom,(
( ( p1 <=> p2)  => ( p1 & ( p2 & p3 ) )) )).

fof(axiom2,axiom,(
( ( p2 <=> p3)  => ( p1 & ( p2 & p3 ) )) )).

fof(axiom3,axiom,(
( ( p3 <=> p1)  => ( p1 & ( p2 & p3 ) )) )).

fof(con,conjecture,(
( p1 & ( p2 & p3 ) )
)).

%--------------------------------------------------------------------------
";
        let mut names = Names::default();
        let seq = parse_sequent(s, &mut names, true, true).unwrap();
        assert_eq!(
            seq.display(&names).to_string(),
            "(p1 ↔ p2) → (p1 ∧ p2 ∧ p3), (p2 ↔ p3) → (p1 ∧ p2 ∧ p3), (p3 ↔ p1) → (p1 ∧ p2 ∧ p3) ⊢ p1 ∧ p2 ∧ p3"
        );
    }
}
