use crate::formula::{Formula, Term};
use indexmap::IndexSet;
use std::fmt;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NamingInfo {
    names: IndexSet<String>,
}

impl NamingInfo {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_id(&mut self, s: String) -> usize {
        let (id, _) = self.names.insert_full(s);
        id
    }

    fn get_name(&self, id: usize) -> String {
        self.names.get_index(id).unwrap_or(&id.to_string()).clone()
    }
}

struct TermDisplay<'a> {
    term: &'a Term,
    inf: &'a NamingInfo,
}

impl fmt::Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Term::*;
        match self.term {
            Var(id) => write!(f, "{}", self.inf.get_name(*id))?,
            Function(id, terms) => write!(
                f,
                "{}({})",
                self.inf.get_name(*id),
                terms
                    .iter()
                    .map(|term| term.display(self.inf).to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            )?,
        }
        Ok(())
    }
}

impl Term {
    fn display<'a>(&'a self, inf: &'a NamingInfo) -> TermDisplay<'a> {
        TermDisplay { term: self, inf }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.display(&NamingInfo::new()))
    }
}

impl Formula {
    /// Returns a string representation of the Formula using the provided NamingInfo.
    pub fn to_str_inf(&self, inf: &NamingInfo) -> String {
        let s = self.to_str_inf_rec(inf);
        s.strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or(&s)
            .into()
    }

    fn to_str_inf_rec(&self, inf: &NamingInfo) -> String {
        use Formula::*;
        match self {
            Predicate(id, terms) => {
                if terms.is_empty() {
                    inf.get_name(*id)
                } else {
                    format!(
                        "{}({})",
                        inf.get_name(*id),
                        terms
                            .iter()
                            .map(|term| term.display(inf).to_string())
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                }
            }
            Not(p) => format!("¬{}", p.to_str_inf_rec(inf)),
            And(l) => match l.as_slice() {
                [] => "true".into(),
                [Implies(p_l, q_l), Implies(p_r, q_r)] if p_l == q_r && q_l == p_r => {
                    format!(
                        "({} ↔ {})",
                        p_l.to_str_inf_rec(inf),
                        q_l.to_str_inf_rec(inf)
                    )
                }
                _ => {
                    format!(
                        "({})",
                        l.iter()
                            .map(|p| p.to_str_inf_rec(inf))
                            .collect::<Vec<_>>()
                            .join(" ∧ ")
                    )
                }
            },
            Or(l) => {
                if l.is_empty() {
                    "false".into()
                } else {
                    format!(
                        "({})",
                        l.iter()
                            .map(|p| p.to_str_inf_rec(inf))
                            .collect::<Vec<_>>()
                            .join(" ∨ ")
                    )
                }
            }
            Implies(p, q) => format!("({} → {})", p.to_str_inf_rec(inf), q.to_str_inf_rec(inf)),
            All(vars, p) => format!(
                "∀{}{}",
                vars.iter()
                    .map(|id| inf.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                p.to_str_inf_rec(inf)
            ),
            Exists(vars, p) => format!(
                "∃{}{}",
                vars.iter()
                    .map(|id| inf.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                p.to_str_inf_rec(inf)
            ),
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str_inf_rec(&NamingInfo::new()))
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    #[test]
    fn test_to_str_inf() {
        let (fml, inf) = parse("P(x)").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "P(x)");

        let (fml, inf) = parse("P(x,f(y,g(z)))").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "P(x,f(y,g(z)))");

        let (fml, inf) = parse("not P").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "¬P");

        let (fml, inf) = parse("P and Q and R and S").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "P ∧ Q ∧ R ∧ S");

        let (fml, inf) = parse("P or Q or R or S").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "P ∨ Q ∨ R ∨ S");

        let (fml, inf) = parse("P to Q to R to S").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "P → (Q → (R → S))");

        let (fml, inf) = parse("P iff Q iff R iff S").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "P ↔ (Q ↔ (R ↔ S))");

        let (fml, inf) = parse("all x,y,z P(x, y, z)").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "∀x,y,zP(x,y,z)");

        let (fml, inf) = parse("ex x,y,z P(x, y, z)").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "∃x,y,zP(x,y,z)");

        let (fml, inf) = parse("P and Q and R to S or T iff U").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "((P ∧ Q ∧ R) → (S ∨ T)) ↔ U");

        let (fml, inf) = parse("(P to Q) and (Q to P)").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "P ↔ Q");

        let (fml, inf) = parse("(P to Q) and (Q to R)").unwrap();
        assert_eq!(fml.to_str_inf(&inf), "(P → Q) ∧ (Q → R)");
    }
}
