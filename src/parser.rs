use crate::formula::{Formula, NamingInfo, Term};
use maplit::{hashmap, hashset};
use regex::Regex;
use std::collections::HashSet;
use unicode_normalization::UnicodeNormalization;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PTerm {
    Var(String),
    Function(String, Vec<PTerm>),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PFormula {
    Predicate(String, Vec<PTerm>),
    Not(Box<PFormula>),
    And(Vec<PFormula>),
    Or(Vec<PFormula>),
    Implies(Box<PFormula>, Box<PFormula>),
    All(Vec<String>, Box<PFormula>),
    Exists(Vec<String>, Box<PFormula>),
}

pub static P_TRUE: PFormula = PFormula::And(vec![]);
pub static P_FALSE: PFormula = PFormula::Or(vec![]);

pub fn parse(s: &str) -> Option<(Formula, NamingInfo)> {
    let s = s.nfkc().collect::<String>().trim().to_string();
    let s = Regex::new(r"\s").unwrap().replace_all(&s, " ");
    let lp = s.chars().filter(|&c| c == '(').count();
    let rp = s.chars().filter(|&c| c == ')').count();
    if lp != rp {
        println!("Parentheses error: Found {lp} left parentheses and {rp} right parentheses.");
        return None;
    }
    let pfml = match parser::formula(&s) {
        Ok(pfml) => pfml,
        Err(e) => {
            println!("Parser error");
            println!(" | ");
            println!(" | {s}");
            println!(" | {}^___", " ".repeat(e.location.column - 1));
            println!(" | ");
            println!(" = expected {}", e.expected);
            return None;
        }
    };
    let (fml, inf) = pfml.into_formula();
    if !fml.check_arity() {
        println!("Error: Predicates and functions must take the same number of arguments.");
        return None;
    }
    if !fml.check_bdd_var() {
        println!("Error: Cannot quantify predicates or functions.");
        return None;
    }
    Some((fml, inf))
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
        p:@ _ iff() _ q:(@) { And(vec![Implies(Box::new(p), Box::new(q)), Implies(Box::new(q), Box::new(p))]) }
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
        --
        p:@ _ and() _ q:(@) {
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
        --
        not() _ p:@ { Not(Box::new(p)) }
        all() _ vs:($var() ++ (_ "," _)) _ p:@ {
            let mut vs: Vec<_> = vs.iter().map(|s| s.to_string()).collect();
            match p {
                All(ws, q) => {
                    vs.extend(ws);
                    All(vs, q)
                }
                p => All(vs, Box::new(p)),
            }
        }
        exists() _ vs:($var() ++ (_ "," _)) _ p:@ {
            let mut vs: Vec<_> = vs.iter().map(|s| s.to_string()).collect();
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
        "(" p:formula() ")" { p }
    } / expected!("formula")

    rule ASCII_ALPHA_GREEK() = ['a'..='z' | 'A'..='Z' | 'α'..='ω' | 'Α'..='Ω' ]
    rule ASCII_DIGIT_HYPHEN_APOSTROPHE() = ['0'..='9' | '_' | '\'' ]
    rule ASCII_ALPHANUMERIC_GREEK_HYPHEN_APOSTROPHE() = ASCII_ALPHA_GREEK() / ASCII_DIGIT_HYPHEN_APOSTROPHE()

    rule var() = ASCII_ALPHA_GREEK() ASCII_DIGIT_HYPHEN_APOSTROPHE()*
    rule function_name() = ASCII_ALPHA_GREEK() ASCII_ALPHANUMERIC_GREEK_HYPHEN_APOSTROPHE()*
    rule predicate_name() = quiet!{ ASCII_ALPHA_GREEK() ASCII_ALPHANUMERIC_GREEK_HYPHEN_APOSTROPHE()* } / expected!("predicate")

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
            PFormula::Predicate(name, pterms) => Formula::Predicate(
                inf.get_id(name),
                pterms
                    .into_iter()
                    .map(|pterm| pterm.into_term(inf))
                    .collect(),
            ),
            PFormula::Not(p) => Formula::Not(Box::new(p.into_formula_rec(inf))),
            PFormula::And(l) => {
                Formula::And(l.into_iter().map(|p| p.into_formula_rec(inf)).collect())
            }
            PFormula::Or(l) => {
                Formula::Or(l.into_iter().map(|p| p.into_formula_rec(inf)).collect())
            }
            PFormula::Implies(p, q) => Formula::Implies(
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

impl Term {
    /// Return the set of all function ids and arity in the term.
    fn get_fns(&self, fns: &mut HashSet<(usize, usize)>) {
        use Term::*;
        match self {
            Var(_) => {}
            Function(id, terms) => {
                fns.insert((*id, terms.len()));
                for term in terms {
                    term.get_fns(fns);
                }
            }
        }
    }
}

impl Formula {
    /// Check if there is a predicate or a function with different number of arguments.
    /// If there is, return false.
    /// This function is mainly for performance improvement for unification.
    fn check_arity(&self) -> bool {
        let mut env = hashmap!();
        for (id, arity) in self.get_preds() {
            if env.get(&id).is_some() {
                return false;
            } else {
                env.insert(id, arity);
            }
        }
        let mut env = hashmap!();
        for (id, arity) in self.get_fns() {
            if env.get(&id).is_some() {
                return false;
            } else {
                env.insert(id, arity);
            }
        }
        true
    }

    /// Check if there is a quantified predicate or function.
    /// If there is, return false.
    fn check_bdd_var(&self) -> bool {
        use Formula::*;
        match self {
            Predicate(_, _) => true,
            Not(p) => p.check_bdd_var(),
            And(l) | Or(l) => l.iter().all(|p| p.check_bdd_var()),
            Implies(p, q) => p.check_bdd_var() && q.check_bdd_var(),
            All(vs, p) | Exists(vs, p) => {
                let vs = vs.iter().cloned().collect();
                let pred_ids: HashSet<_> = p.get_preds().into_iter().map(|(id, _)| id).collect();
                if !pred_ids.is_disjoint(&vs) {
                    return false;
                }
                let fn_ids: HashSet<_> = p.get_fns().into_iter().map(|(id, _)| id).collect();
                if !fn_ids.is_disjoint(&vs) {
                    return false;
                }
                true
            }
        }
    }

    /// Return the set of all function ids and arity in the formula.
    fn get_fns(&self) -> HashSet<(usize, usize)> {
        let mut fns = hashset!();
        self.get_fns_rec(&mut fns);
        fns
    }

    fn get_fns_rec(&self, fns: &mut HashSet<(usize, usize)>) {
        use Formula::*;
        match self {
            Predicate(_, terms) => {
                for term in terms {
                    term.get_fns(fns);
                }
            }
            And(l) | Or(l) => {
                for p in l {
                    p.get_fns_rec(fns);
                }
            }
            Implies(p, q) => {
                p.get_fns_rec(fns);
                q.get_fns_rec(fns);
            }
            Not(p) | All(_, p) | Exists(_, p) => p.get_fns_rec(fns),
        }
    }

    /// Return the set of all predicate ids and arity in the formula.
    fn get_preds(&self) -> HashSet<(usize, usize)> {
        let mut preds = hashset!();
        self.get_preds_rec(&mut preds);
        preds
    }

    fn get_preds_rec(&self, preds: &mut HashSet<(usize, usize)>) {
        use Formula::*;
        match self {
            Predicate(id, terms) => {
                preds.insert((*id, terms.len()));
            }
            Not(p) => p.get_preds_rec(preds),
            And(l) | Or(l) => {
                for p in l {
                    p.get_preds_rec(preds);
                }
            }
            Implies(p, q) => {
                p.get_preds_rec(preds);
                q.get_preds_rec(preds);
            }
            All(_, p) | Exists(_, p) => p.get_preds_rec(preds),
        }
    }

    pub fn universal_quantify(self) -> Self {
        use Formula::All;
        let mut fv: Vec<_> = self.free_vars().into_iter().collect();
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
                vec!["x".into()],
                Box::new(Predicate("P".into(), vec![Var("x".into())]))
            )
        );
        assert_eq!(
            formula("all x, y P(x, y)").unwrap(),
            All(
                vec!["x".into(), "y".into()],
                Box::new(Predicate(
                    "P".into(),
                    vec![Var("x".into()), Var("y".into())]
                ))
            )
        );
        assert_eq!(
            formula("ex x P(x)").unwrap(),
            Exists(
                vec!["x".into()],
                Box::new(Predicate("P".into(), vec![Var("x".into())]))
            )
        );
        assert_eq!(
            formula("ex x, y P(x, y)").unwrap(),
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
                vec!["x".into(), "y".into(), "z".into(), "u".into()],
                Box::new(Exists(
                    vec!["v".into(), "w".into()],
                    Box::new(All(vec!["h".into()], Box::new(formula("P").unwrap())))
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
            let (fml, inf) = parse(s).unwrap();
            assert_eq!(fml.to_str_inf(&inf), expected);
        }
    }

    #[test]
    fn test_check_arity() {
        let (fml, _) = formula("P and P").unwrap().into_formula();
        assert!(fml.check_arity());
        let (fml, _) = formula("P and P(x)").unwrap().into_formula();
        assert!(!fml.check_arity());
        let (fml, _) = formula("P(x) and P(x,y)").unwrap().into_formula();
        assert!(!fml.check_arity());
        let (fml, _) = formula("P(f(x), f(x))").unwrap().into_formula();
        assert!(fml.check_arity());
        let (fml, _) = formula("P(f(x), f(x,y))").unwrap().into_formula();
        assert!(!fml.check_arity());
    }

    #[test]
    fn test_check_bdd_var() {
        let (fml, _) = formula("all x,y P(f(x,y))").unwrap().into_formula();
        assert!(fml.check_bdd_var());
        let (fml, _) = formula("all f all x,y P(f(x,y))").unwrap().into_formula();
        assert!(!fml.check_bdd_var());
        let (fml, _) = formula("all P all x,y P(f(x,y))").unwrap().into_formula();
        assert!(!fml.check_bdd_var());
    }

    #[test]
    fn test_universal_quantify() {
        let mut inf = NamingInfo::new();

        let fml = formula("all x,y P(f(x,y))")
            .unwrap()
            .into_formula_rec(&mut inf);
        assert_eq!(fml.clone().universal_quantify(), fml);

        let fml1 = formula("P(f(x,y))").unwrap().into_formula_rec(&mut inf);
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
            .into_formula_rec(&mut inf);
        assert_eq!(fml2.universal_quantify(), fml);
    }
}
