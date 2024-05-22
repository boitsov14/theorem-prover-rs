use crate::formula::{Formula, Sequent, Term};
use itertools::Itertools;
use regex::Regex;
use std::fmt;

#[derive(Clone, Debug, Default)]
pub struct Names {
    names: Vec<String>,
}

impl Names {
    pub fn get_id(&mut self, s: String) -> usize {
        for (i, name) in self.names.iter().enumerate() {
            if name == &s {
                return i;
            }
        }
        self.names.push(s);
        self.names.len() - 1
    }

    fn get_fresh_name(&self, s: String) -> String {
        let mut s = s;
        while self.names.contains(&s) {
            s.push('\'');
        }
        s
    }

    pub fn get_fresh_id(&mut self, s: String) -> usize {
        let s = self.get_fresh_name(s);
        self.get_id(s)
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn get_name(&self, id: usize) -> String {
        self.names
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("?_{}", id))
    }
}

pub trait Latex {
    fn to_latex(&self) -> String;
}

pub struct TermDisplay<'a> {
    term: &'a Term,
    names: &'a Names,
}

impl fmt::Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Term::*;
        match self.term {
            Var(id) => write!(f, "{}", self.names.get_name(*id))?,
            Func(id, terms) => write!(
                f,
                "{}({})",
                self.names.get_name(*id),
                terms
                    .iter()
                    .map(|term| term.display(self.names).to_string())
                    .collect_vec()
                    .join(",")
            )?,
        }
        Ok(())
    }
}

impl Term {
    pub fn display<'a>(&'a self, names: &'a Names) -> TermDisplay<'a> {
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
            Pred(id, terms) => {
                if terms.is_empty() {
                    write!(f, "{}", self.names.get_name(*id))?;
                } else {
                    write!(
                        f,
                        "{}({})",
                        self.names.get_name(*id),
                        terms
                            .iter()
                            .map(|term| term.display(self.names).to_string())
                            .collect_vec()
                            .join(",")
                    )?;
                }
            }
            Not(p) => write!(f, "¬{}", p.display_inner(self.names))?,
            And(l) => {
                if l.is_empty() {
                    write!(f, "true")?;
                } else {
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
            }
            Or(l) => {
                if l.is_empty() {
                    write!(f, "false")?;
                } else {
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
            All(vars, p) => write!(
                f,
                "∀{}{}",
                vars.iter()
                    .map(|id| self.names.get_name(*id))
                    .collect_vec()
                    .join(","),
                p.display_inner(self.names)
            )?,
            Ex(vars, p) => write!(
                f,
                "∃{}{}",
                vars.iter()
                    .map(|id| self.names.get_name(*id))
                    .collect_vec()
                    .join(","),
                p.display_inner(self.names)
            )?,
        }
        Ok(())
    }
}

impl Latex for FormulaDisplay<'_> {
    fn to_latex(&self) -> String {
        let str = self
            .to_string()
            .replace("true", r"\top")
            .replace("false", r"\bot")
            .replace('¬', r"\lnot ")
            .replace('∧', r"\land")
            .replace('∨', r"\lor")
            .replace('→', r"\rightarrow")
            .replace('↔', r"\leftrightarrow")
            .replace('∀', r"\forall ")
            .replace('∃', r"\exists ")
            .replace('_', r"\_");

        Regex::new(r"v\\_(\d+)")
            .unwrap()
            .replace_all(&str, "v_{$1}")
            .to_string()
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
                .map(|fml| fml.display(self.names).to_string())
                .collect_vec()
                .join(", "),
            self.sequent
                .suc
                .iter()
                .map(|fml| fml.display(self.names).to_string())
                .collect_vec()
                .join(", ")
        )?;
        Ok(())
    }
}

impl Latex for SequentDisplay<'_> {
    fn to_latex(&self) -> String {
        format!(
            r"{} &\vdash {}",
            self.sequent
                .ant
                .iter()
                .map(|fml| fml.display(self.names).to_latex())
                .collect_vec()
                .join(", "),
            self.sequent
                .suc
                .iter()
                .map(|fml| fml.display(self.names).to_latex())
                .collect_vec()
                .join(", ")
        )
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
