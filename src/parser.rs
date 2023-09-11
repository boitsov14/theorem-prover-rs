use crate::formula::{Formula, NamingInfo, Term};
use regex::Regex;
use std::collections::HashSet;
use unicode_normalization::UnicodeNormalization;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PTerm {
    Var(String),
    Function(String, Vec<PTerm>),
}

// TODO: 2023/09/11 Formula or PFormula
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PFormula {
    Predicate(String, Vec<PTerm>),
    Not(Box<PFormula>),
    And(Vec<PFormula>),
    Or(Vec<PFormula>),
    Implies(Box<PFormula>, Box<PFormula>),
    Iff(Box<PFormula>, Box<PFormula>),
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
        println!("Parentheses error: Found {lp} left parentheses and {rp} right parentheses");
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
    Some((fml, inf))
    // TODO: 2023/08/27 functionやpredicateやbdd var(Duplicated Bounded Variables)をquantifyしていないかのチェック
    // TODO: 2023/09/11 同じpredicate，functionで異なる個数の引数をもつものがないかチェック
    // TODO: 2023/09/06 自由変数をすべてallにする
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
        p:@ _ iff() _ q:(@) { Iff(Box::new(p), Box::new(q)) }
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

impl Formula {
    /// Return the set of all bounded variables in the formula.
    fn bdd_vs(&self, vars: &mut HashSet<usize>) {
        use Formula::*;
        match self {
            Predicate(_, _) => {}
            Not(p) => p.bdd_vs(vars),
            And(l) | Or(l) => {
                for p in l {
                    p.bdd_vs(vars);
                }
            }
            Implies(p, q) | Iff(p, q) => {
                p.bdd_vs(vars);
                q.bdd_vs(vars);
            }
            All(vs, p) | Exists(vs, p) => {
                vars.extend(vs);
                p.bdd_vs(vars);
            }
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
            term("f(x, y)").unwrap(),
            Function("f".into(), vec![Var("x".into()), Var("y".into())])
        );
        assert_eq!(
            term("f(x, g(y))").unwrap(),
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
        assert_eq!(formula("true").unwrap(), P_TRUE);
        assert_eq!(formula("false").unwrap(), P_FALSE);
        assert_eq!(formula("P").unwrap(), Predicate("P".into(), vec![]));
        assert_eq!(
            formula("P(x)").unwrap(),
            Predicate("P".into(), vec![Var("x".into())])
        );
        assert_eq!(
            formula("P(x, g(y))").unwrap(),
            Predicate(
                "P".into(),
                vec![Var("x".into()), Function("g".into(), vec![Var("y".into())])]
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
            Iff(
                Box::new(Predicate("P".into(), vec![])),
                Box::new(Predicate("Q".into(), vec![]))
            )
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
}
