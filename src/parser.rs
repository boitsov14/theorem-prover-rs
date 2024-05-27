use crate::formula::{Formula, Sequent, Term};
use crate::naming::Names;
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
    Pred(String, Vec<PTerm>),
    Not(Box<PFormula>),
    And(Vec<PFormula>),
    Or(Vec<PFormula>),
    To(Box<PFormula>, Box<PFormula>),
    Iff(Box<PFormula>, Box<PFormula>),
    All(Vec<String>, Box<PFormula>),
    Ex(Vec<String>, Box<PFormula>),
}

#[derive(Clone, Debug)]
struct PSequent {
    ant: Vec<PFormula>,
    suc: Vec<PFormula>,
}

static P_TRUE: PFormula = PFormula::And(vec![]);
static P_FALSE: PFormula = PFormula::Or(vec![]);

/// Parses a term.
pub(super) fn parse_term(s: &str, names: &mut Names) -> Result<Term, Error> {
    let s = modify_string(s);
    check_parentheses(&s)?;
    let pterm = parser::term(&s).map_err(|e| Error::Peg { s: s.into(), e })?;
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
    let pfml = parser::formula(&s).map_err(|e| Error::Peg { s: s.into(), e })?;
    let mut fml = pfml.into_formula(names);
    if modify_formula {
        fml.modify(names);
    }
    Ok(fml)
}

/// Parses a sequent.
fn parse_sequent(
    s: &str,
    names: &mut Names,
    modify_formula: bool,
    tptp: bool,
) -> Result<Sequent, Error> {
    let s = if tptp { modify_tptp(s) } else { s.to_string() };
    let s = modify_string(&s);
    check_parentheses(&s)?;
    let pseq = parser::sequent(&s).map_err(|e| Error::Peg { s: s.into(), e })?;
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
    Regex::new(r"\s").unwrap().replace_all(&s, " ").to_string()
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

// TODO: 2024/05/21 削除
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
    let pfml = parser::formula(&s).map_err(|e| Error::Peg { s: s.into(), e })?;
    let mut names = Names::default();
    let mut fml = pfml.into_formula(&mut names);
    // Modify the formula.
    fml.flatten();
    fml.unique();
    fml.rename_nested_bdd_vars(&mut names, &hashmap!());
    fml.rename_bdd_vars(&mut names);
    fml.subst_free_vars_with_constants(&hashset!());
    Ok((fml, names))
}

pub fn modify_tptp(s: &str) -> String {
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
        p_true() { P_TRUE.clone() } /
        p_false() { P_FALSE.clone() } /
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
        p:@ _ or() _ q:(@) { Or(vec![p, q]) }
        --
        p:@ _ and() _ q:(@) { And(vec![p, q]) }
        --
        not() _ p:@ { Not(Box::new(p)) }
        all() _ vs:($bdd_var_id() ++ (_ "," _)) _ p:@ { All(vs.iter().map(|&s| s.to_string()).collect(), Box::new(p)) }
        ex() _ vs:($bdd_var_id() ++ (_ "," _)) _ p:@ { Ex(vs.iter().map(|&s| s.to_string()).collect(), Box::new(p)) }
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
    rule not() = quiet!{ "¬" / "~" / "not" / r"\lnot" / r"\neg" } / expected!("'¬'")
    rule and() = quiet!{ "∧" / r"/\" / "&" / "and" / r"\land" / r"\wedge" } / expected!("'∧'")
    rule or() = quiet!{ "∨" / r"\/" / "|" / "or" / r"\lor" / r"\vee" } / expected!("'∨'")
    rule to() = quiet!{ "→" / "->" / "to" / r"\rightarrow" / r"\to" } / expected!("'→'")
    rule iff() = quiet!{ "↔" / "<->" / "iff" / r"\leftrightarrow" } / expected!("'↔'")
    rule all() = quiet!{ "∀" / "!" / "all" / r"\forall" } / expected!("'∀'")
    rule ex() = quiet!{ "∃" / "?" / "ex" / r"\exists" } / expected!("'∃'")
    rule turnstile() = quiet!{ "⊢" / "|-" / "├" / "┣" / r"\vdash" } / expected!("'⊢'")
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
            Self::To(p, q) => Formula::To(
                Box::new(p.into_formula(names)),
                Box::new(q.into_formula(names)),
            ),
            Self::Iff(p, q) => Formula::Iff(
                Box::new(p.into_formula(names)),
                Box::new(q.into_formula(names)),
            ),
            Self::All(vs, p) => Formula::All(
                vs.into_iter().map(|name| names.get_id(name)).collect(),
                Box::new(p.into_formula(names)),
            ),
            Self::Ex(vs, p) => Formula::Ex(
                vs.into_iter().map(|name| names.get_id(name)).collect(),
                Box::new(p.into_formula(names)),
            ),
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
                p.flatten();
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
    /// Converts `∀x,x P(x)` to `∀x P(x)`.
    ///
    /// Converts `∃x,x P(x)` to `∃x P(x)`.
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
    /// Converts `∀x (P(x) ∧ ∀x Q(x))` to `∀x (P(x) ∧ ∀x' Q(x'))`
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
    /// Converts `∀P P(P)` to `∀P' P(P')`
    ///
    /// Converts `∀f P(f(f))` to `∀f' P(f(f'))`
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
    /// Converts `P(x) ∧ ∀y Q(y)` to `P(x()) ∧ ∀y Q(y)`
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
                bdd_vars.extend(vs.iter().cloned());
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
        assert_eq!(pfml("true"), P_TRUE);
        assert_eq!(pfml("false"), P_FALSE);
        assert_eq!(pfml("P"), Pred("P".into(), vec![]));
        assert_eq!(pfml("P(x)"), Pred("P".into(), vec![pterm("x")]));
        assert_eq!(
            pfml("P(x,f(y),z)"),
            Pred("P".into(), vec![pterm("x"), pterm("f(y)"), pterm("z")])
        );
        assert_eq!(pfml("¬P"), Not(Box::new(pfml("P"))));
        assert_eq!(pfml("P ∧ Q"), And(vec![pfml("P"), pfml("Q")]));
        assert_eq!(pfml("P ∨ Q"), Or(vec![pfml("P"), pfml("Q")]));
        assert_eq!(pfml("P → Q"), To(Box::new(pfml("P")), Box::new(pfml("Q"))));
        assert_eq!(pfml("P ↔ Q"), Iff(Box::new(pfml("P")), Box::new(pfml("Q"))));
        assert_eq!(
            pfml("∀xP(x)"),
            All(vec!["x".into()], Box::new(pfml("P(x)")))
        );
        assert_eq!(
            pfml("∀x,yP(x,y)"),
            All(vec!["x".into(), "y".into()], Box::new(pfml("P(x,y)")))
        );
        assert_eq!(pfml("∃xP(x)"), Ex(vec!["x".into()], Box::new(pfml("P(x)"))));
        assert_eq!(
            pfml("∃x,yP(x,y)"),
            Ex(vec!["x".into(), "y".into()], Box::new(pfml("P(x,y)")))
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
        assert_eq!(pfml("¬P ∧ Q ∨ R → S"), {
            To(
                Box::new(Or(vec![
                    And(vec![Not(Box::new(pfml("P"))), pfml("Q")]),
                    pfml("R"),
                ])),
                Box::new(pfml("S")),
            )
        });
    }

    #[test]
    fn test_parse_fml_nfkc() {
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
    #[case("true ∧ P ∧ true ∧ Q ∧ true" => "P ∧ Q")]
    #[case("false ∨ P ∨ false ∨ Q ∨ false" => "P ∨ Q")]
    #[case("(P ∧ true ∧ P ∧ false ∨ P ∧ P) → P" => "((P ∧ false) ∨ P) → P")]
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
    #[case("P ∧ true", "P")]
    #[case("P ∨ false", "P")]
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
            modify_tptp(s),
            "((s)) -> (((( ~(( t => r) ) => p) )) -> ((( ~(( ( p => q)  & ( t => r)  )) => ( ~(~(p)) & ( s & s ) )) )))"
        )
    }
}
