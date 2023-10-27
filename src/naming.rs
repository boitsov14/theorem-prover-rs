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

pub struct FormulaDisplay<'a> {
    formula: &'a Formula,
    inf: &'a NamingInfo,
    is_inner: bool,
}

impl fmt::Display for FormulaDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Formula::*;
        match self.formula {
            Predicate(id, terms) => {
                if terms.is_empty() {
                    write!(f, "{}", self.inf.get_name(*id))?;
                } else {
                    write!(
                        f,
                        "{}({})",
                        self.inf.get_name(*id),
                        terms
                            .iter()
                            .map(|term| term.display(self.inf).to_string())
                            .collect::<Vec<_>>()
                            .join(",")
                    )?;
                }
            }
            Not(p) => write!(f, "¬{}", p.display_inner(self.inf))?,
            And(l) => match l.as_slice() {
                [] => write!(f, "true")?,
                [Implies(p_l, q_l), Implies(p_r, q_r)] if p_l == q_r && q_l == p_r => {
                    if self.is_inner {
                        write!(f, "(")?;
                    }
                    write!(
                        f,
                        "{} ↔ {}",
                        p_l.display_inner(self.inf),
                        q_l.display_inner(self.inf)
                    )?;
                    if self.is_inner {
                        write!(f, ")")?;
                    }
                }
                _ => {
                    if self.is_inner {
                        write!(f, "(")?;
                    }
                    write!(
                        f,
                        "{}",
                        l.iter()
                            .map(|p| p.display_inner(self.inf).to_string())
                            .collect::<Vec<_>>()
                            .join(" ∧ ")
                    )?;
                    if self.is_inner {
                        write!(f, ")")?;
                    }
                }
            },
            Or(l) => match l.as_slice() {
                [] => write!(f, "false")?,
                _ => {
                    if self.is_inner {
                        write!(f, "(")?;
                    }
                    write!(
                        f,
                        "{}",
                        l.iter()
                            .map(|p| p.display_inner(self.inf).to_string())
                            .collect::<Vec<_>>()
                            .join(" ∨ ")
                    )?;
                    if self.is_inner {
                        write!(f, ")")?;
                    }
                }
            },
            Implies(p, q) => {
                if self.is_inner {
                    write!(f, "(")?;
                }
                write!(
                    f,
                    "{} → {}",
                    p.display_inner(self.inf),
                    q.display_inner(self.inf)
                )?;
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            All(vars, p) => write!(
                f,
                "∀{}{}",
                vars.iter()
                    .map(|id| self.inf.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                p.display_inner(self.inf)
            )?,
            Exists(vars, p) => write!(
                f,
                "∃{}{}",
                vars.iter()
                    .map(|id| self.inf.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                p.display_inner(self.inf)
            )?,
        }
        Ok(())
    }
}

impl Formula {
    pub fn display<'a>(&'a self, inf: &'a NamingInfo) -> FormulaDisplay<'a> {
        FormulaDisplay {
            formula: self,
            inf,
            is_inner: false,
        }
    }
    fn display_inner<'a>(&'a self, inf: &'a NamingInfo) -> FormulaDisplay<'a> {
        FormulaDisplay {
            formula: self,
            inf,
            is_inner: true,
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display(&NamingInfo::new()))
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    #[test]
    fn test_display() {
        let (fml, inf) = parse("P(x)").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "P(x)");

        let (fml, inf) = parse("P(x,f(y,g(z)))").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "P(x,f(y,g(z)))");

        let (fml, inf) = parse("not P").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "¬P");

        let (fml, inf) = parse("P and Q and R and S").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "P ∧ Q ∧ R ∧ S");

        let (fml, inf) = parse("P or Q or R or S").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "P ∨ Q ∨ R ∨ S");

        let (fml, inf) = parse("P to Q to R to S").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "P → (Q → (R → S))");

        let (fml, inf) = parse("P iff Q iff R iff S").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "P ↔ (Q ↔ (R ↔ S))");

        let (fml, inf) = parse("all x,y,z P(x, y, z)").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "∀x,y,zP(x,y,z)");

        let (fml, inf) = parse("ex x,y,z P(x, y, z)").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "∃x,y,zP(x,y,z)");

        let (fml, inf) = parse("P and Q and R to S or T iff U").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "((P ∧ Q ∧ R) → (S ∨ T)) ↔ U");

        let (fml, inf) = parse("(P to Q) and (Q to P)").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "P ↔ Q");

        let (fml, inf) = parse("(P to Q) and (Q to R)").unwrap();
        assert_eq!(fml.display(&inf).to_string(), "(P → Q) ∧ (Q → R)");
    }
}
