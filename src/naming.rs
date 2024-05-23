use crate::formula::{Formula, Sequent, Term};
use itertools::Itertools;
use regex::Regex;
use std::fmt;

#[derive(Clone, Debug, Default)]
pub struct Names {
    names: Vec<String>,
}

impl Names {
    /// The number of names.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Retrieves the ID associated with a given name.
    /// If the name is not found, it is added to the names.
    pub(super) fn get_id(&mut self, name: String) -> usize {
        self.names
            .iter()
            .position(|s| s == &name)
            .unwrap_or_else(|| {
                self.names.push(name);
                self.names.len() - 1
            })
    }

    /// Generates a fresh name by appending a single quote (') to the given name.
    fn gen_fresh_name(&self, mut name: String) -> String {
        while self.names.contains(&name) {
            name.push('\'');
        }
        name
    }

    /// Retrieves the name associated with a given ID.
    /// If the name is not found, a placeholder name is returned.
    pub(super) fn get_name(&self, id: usize) -> String {
        self.names
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("?_{}", id))
    }

    /// Generates a fresh name and retrieves the ID associated with it.
    pub(super) fn gen_fresh_id(&mut self, id: usize) -> usize {
        self.get_id(self.gen_fresh_name(self.get_name(id)))
    }
}

pub(super) struct TermDisplay<'a> {
    term: &'a Term,
    names: &'a Names,
}

impl fmt::Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Term::*;
        write!(
            f,
            "{}",
            match self.term {
                Var(id) => self.names.get_name(*id),
                Func(id, ts) if ts.is_empty() => self.names.get_name(*id),
                Func(id, ts) => format!(
                    "{}({})",
                    self.names.get_name(*id),
                    ts.iter()
                        .map(|t| t.display(self.names).to_string())
                        .collect_vec()
                        .join(",")
                ),
            }
        )
    }
}

impl Term {
    pub(super) fn display<'a>(&'a self, names: &'a Names) -> TermDisplay<'a> {
        TermDisplay { term: self, names }
    }
}

pub struct FormulaDisplay<'a> {
    formula: &'a Formula,
    names: &'a Names,
    is_inner: bool,
}

impl fmt::Display for FormulaDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Formula::*;
        match self.formula {
            Pred(id, ts) if ts.is_empty() => write!(f, "{}", self.names.get_name(*id))?,
            Pred(id, ts) => write!(
                f,
                "{}({})",
                self.names.get_name(*id),
                ts.iter()
                    .map(|t| t.display(self.names).to_string())
                    .collect_vec()
                    .join(",")
            )?,
            Not(p) => write!(f, "¬{}", p.display_inner(self.names))?,
            And(l) if l.is_empty() => write!(f, "true")?,
            And(l) => {
                if self.is_inner {
                    write!(f, "(")?;
                }
                write!(
                    f,
                    "{}",
                    l.iter()
                        .map(|p| p.display_inner(self.names).to_string())
                        .collect_vec()
                        .join(" ∧ ")
                )?;
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            Or(l) if l.is_empty() => write!(f, "false")?,
            Or(l) => {
                if self.is_inner {
                    write!(f, "(")?;
                }
                write!(
                    f,
                    "{}",
                    l.iter()
                        .map(|p| p.display_inner(self.names).to_string())
                        .collect_vec()
                        .join(" ∨ ")
                )?;
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            To(p, q) => {
                if self.is_inner {
                    write!(f, "(")?;
                }
                write!(
                    f,
                    "{} → {}",
                    p.display_inner(self.names),
                    q.display_inner(self.names)
                )?;
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            Iff(p, q) => {
                if self.is_inner {
                    write!(f, "(")?;
                }
                write!(
                    f,
                    "{} ↔ {}",
                    p.display_inner(self.names),
                    q.display_inner(self.names)
                )?;
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            All(vs, p) => write!(
                f,
                "{}{}",
                vs.iter()
                    .map(|v| format!("∀{}", self.names.get_name(*v)))
                    .collect::<String>(),
                p.display_inner(self.names)
            )?,
            Ex(vs, p) => write!(
                f,
                "∃{}{}",
                vs.iter()
                    .map(|v| format!("∃{}", self.names.get_name(*v)))
                    .collect::<String>(),
                p.display_inner(self.names)
            )?,
        }
        Ok(())
    }
}

impl Formula {
    pub fn display<'a>(&'a self, names: &'a Names) -> FormulaDisplay<'a> {
        FormulaDisplay {
            formula: self,
            names,
            is_inner: false,
        }
    }
    fn display_inner<'a>(&'a self, names: &'a Names) -> FormulaDisplay<'a> {
        FormulaDisplay {
            formula: self,
            names,
            is_inner: true,
        }
    }
}

pub struct SequentDisplay<'a> {
    sequent: &'a Sequent,
    names: &'a Names,
}

impl fmt::Display for SequentDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ⊢ {}",
            self.sequent
                .ant
                .iter()
                .map(|p| p.display(self.names).to_string())
                .collect_vec()
                .join(", "),
            self.sequent
                .suc
                .iter()
                .map(|p| p.display(self.names).to_string())
                .collect_vec()
                .join(", ")
        )?;
        Ok(())
    }
}

impl SequentDisplay<'_> {
    pub(super) fn to_latex(&self) -> String {
        let s = self.to_string();
        to_latex(&s)
    }
}

impl Sequent {
    pub fn display<'a>(&'a self, names: &'a Names) -> SequentDisplay<'a> {
        SequentDisplay {
            sequent: self,
            names,
        }
    }
}

fn to_latex(s: &str) -> String {
    let s = s
        .replace("true", r"\top")
        .replace("false", r"\bot")
        .replace('¬', r"\lnot ")
        .replace('∧', r"\land")
        .replace('∨', r"\lor")
        .replace('→', r"\rightarrow")
        .replace('↔', r"\leftrightarrow")
        .replace('∀', r"\forall ")
        .replace('∃', r"\exists ")
        .replace('⊢', r"&\vdash ")
        .replace('_', r"\_");

    Regex::new(r"v\\_(\d+)")
        .unwrap()
        .replace_all(&s, "v_{$1}")
        .to_string()
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    #[test]
    fn test_display() {
        let (fml, names) = parse("P(x)").unwrap();
        assert_eq!(fml.display(&names).to_string(), "P(x)");

        let (fml, names) = parse("P(x,f(y,g(z)))").unwrap();
        assert_eq!(fml.display(&names).to_string(), "P(x,f(y,g(z)))");

        let (fml, names) = parse("not P").unwrap();
        assert_eq!(fml.display(&names).to_string(), "¬P");

        let (fml, names) = parse("P and Q and R and S").unwrap();
        assert_eq!(fml.display(&names).to_string(), "P ∧ Q ∧ R ∧ S");

        let (fml, names) = parse("P or Q or R or S").unwrap();
        assert_eq!(fml.display(&names).to_string(), "P ∨ Q ∨ R ∨ S");

        let (fml, names) = parse("P to Q to R to S").unwrap();
        assert_eq!(fml.display(&names).to_string(), "P → (Q → (R → S))");

        let (fml, names) = parse("P iff Q iff R iff S").unwrap();
        assert_eq!(fml.display(&names).to_string(), "P ↔ (Q ↔ (R ↔ S))");

        let (fml, names) = parse("all x,y,z P(x, y, z)").unwrap();
        assert_eq!(fml.display(&names).to_string(), "∀x,y,zP(x,y,z)");

        let (fml, names) = parse("ex x,y,z P(x, y, z)").unwrap();
        assert_eq!(fml.display(&names).to_string(), "∃x,y,zP(x,y,z)");

        let (fml, names) = parse("P and Q and R to S or T iff U").unwrap();
        assert_eq!(
            fml.display(&names).to_string(),
            "((P ∧ Q ∧ R) → (S ∨ T)) ↔ U"
        );

        let (fml, names) = parse("(P to Q) and (Q to P)").unwrap();
        assert_eq!(fml.display(&names).to_string(), "P ↔ Q");

        let (fml, names) = parse("(P to Q) and (Q to R)").unwrap();
        assert_eq!(fml.display(&names).to_string(), "(P → Q) ∧ (Q → R)");
    }
}
