use crate::formula::{Formula, Term};
use crate::prover::Sequent;
use std::fmt;

#[derive(Clone, Debug, Default)]
pub struct EntitiesInfo {
    names: Vec<Option<String>>,
}

impl EntitiesInfo {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_id(&mut self, s: String) -> usize {
        self.names
            .iter()
            .position(|name| name.as_deref() == Some(&s))
            .unwrap_or_else(|| {
                self.names.push(Some(s));
                self.names.len() - 1
            })
    }

    pub fn make_new_empty_id(&mut self) -> usize {
        self.names.push(None);
        self.names.len() - 1
    }

    fn get_name(&self, id: usize) -> String {
        self.names
            .get(id)
            .and_then(|name| name.clone())
            .unwrap_or_else(|| id.to_string())
    }
}

pub trait Latex {
    fn to_latex(&self) -> String;
}

struct TermDisplay<'a> {
    term: &'a Term,
    entities: &'a EntitiesInfo,
}

impl fmt::Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Term::*;
        match self.term {
            Var(id) => write!(f, "{}", self.entities.get_name(*id))?,
            Function(id, terms) => write!(
                f,
                "{}({})",
                self.entities.get_name(*id),
                terms
                    .iter()
                    .map(|term| term.display(self.entities).to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            )?,
        }
        Ok(())
    }
}

impl Term {
    fn display<'a>(&'a self, entities: &'a EntitiesInfo) -> TermDisplay<'a> {
        TermDisplay {
            term: self,
            entities,
        }
    }
}

// TODO: 2023/12/07 不要なら消したい（Formulaも同様）
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.display(&EntitiesInfo::new()))
    }
}

pub struct FormulaDisplay<'a> {
    formula: &'a Formula,
    entities: &'a EntitiesInfo,
    is_inner: bool,
}

impl fmt::Display for FormulaDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Formula::*;
        match self.formula {
            Predicate(id, terms) => {
                if terms.is_empty() {
                    write!(f, "{}", self.entities.get_name(*id))?;
                } else {
                    write!(
                        f,
                        "{}({})",
                        self.entities.get_name(*id),
                        terms
                            .iter()
                            .map(|term| term.display(self.entities).to_string())
                            .collect::<Vec<_>>()
                            .join(",")
                    )?;
                }
            }
            Not(p) => write!(f, "¬{}", p.display_inner(self.entities))?,
            And(l) => match l.as_slice() {
                [] => write!(f, "true")?,
                [Implies(p_l, q_l), Implies(p_r, q_r)] if p_l == q_r && q_l == p_r => {
                    if self.is_inner {
                        write!(f, "(")?;
                    }
                    write!(
                        f,
                        "{} ↔ {}",
                        p_l.display_inner(self.entities),
                        q_l.display_inner(self.entities)
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
                            .map(|p| p.display_inner(self.entities).to_string())
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
                            .map(|p| p.display_inner(self.entities).to_string())
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
                    p.display_inner(self.entities),
                    q.display_inner(self.entities)
                )?;
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            All(vars, p) => write!(
                f,
                "∀{}{}",
                vars.iter()
                    .map(|id| self.entities.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                p.display_inner(self.entities)
            )?,
            Exists(vars, p) => write!(
                f,
                "∃{}{}",
                vars.iter()
                    .map(|id| self.entities.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                p.display_inner(self.entities)
            )?,
        }
        Ok(())
    }
}

impl Latex for FormulaDisplay<'_> {
    fn to_latex(&self) -> String {
        self.to_string()
            .replace("true", r"\top")
            .replace("false", r"\bot")
            .replace('¬', r"\lnot ")
            .replace('∧', r"\land")
            .replace('∨', r"\lor")
            .replace('→', r"\rightarrow")
            .replace('↔', r"\leftrightarrow")
            .replace('∀', r"\forall ")
            .replace('∃', r"\exists ")
            .replace('_', r"\_")
    }
}

impl Formula {
    pub fn display<'a>(&'a self, entities: &'a EntitiesInfo) -> FormulaDisplay<'a> {
        FormulaDisplay {
            formula: self,
            entities,
            is_inner: false,
        }
    }
    fn display_inner<'a>(&'a self, entities: &'a EntitiesInfo) -> FormulaDisplay<'a> {
        FormulaDisplay {
            formula: self,
            entities,
            is_inner: true,
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display(&EntitiesInfo::new()))
    }
}

pub struct SequentDisplay<'a, 'b> {
    sequent: &'a Sequent<'b>,
    entities: &'a EntitiesInfo,
}

impl fmt::Display for SequentDisplay<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ⊢ {}",
            self.sequent
                .ant
                .iter()
                .map(|fml| fml.display(self.entities).to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.sequent
                .suc
                .iter()
                .map(|fml| fml.display(self.entities).to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        Ok(())
    }
}

impl Latex for SequentDisplay<'_, '_> {
    fn to_latex(&self) -> String {
        format!(
            r"{} &\vdash {}",
            self.sequent
                .ant
                .iter()
                .map(|fml| fml.display(self.entities).to_latex())
                .collect::<Vec<_>>()
                .join(", "),
            self.sequent
                .suc
                .iter()
                .map(|fml| fml.display(self.entities).to_latex())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<'b> Sequent<'b> {
    pub fn display<'a>(&'a self, entities: &'a EntitiesInfo) -> SequentDisplay<'a, 'b> {
        SequentDisplay {
            sequent: self,
            entities,
        }
    }
}

impl fmt::Display for Sequent<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display(&EntitiesInfo::new()))
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    #[test]
    fn test_display() {
        let (fml, entities) = parse("P(x)").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "P(x)");

        let (fml, entities) = parse("P(x,f(y,g(z)))").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "P(x,f(y,g(z)))");

        let (fml, entities) = parse("not P").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "¬P");

        let (fml, entities) = parse("P and Q and R and S").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "P ∧ Q ∧ R ∧ S");

        let (fml, entities) = parse("P or Q or R or S").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "P ∨ Q ∨ R ∨ S");

        let (fml, entities) = parse("P to Q to R to S").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "P → (Q → (R → S))");

        let (fml, entities) = parse("P iff Q iff R iff S").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "P ↔ (Q ↔ (R ↔ S))");

        let (fml, entities) = parse("all x,y,z P(x, y, z)").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "∀x,y,zP(x,y,z)");

        let (fml, entities) = parse("ex x,y,z P(x, y, z)").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "∃x,y,zP(x,y,z)");

        let (fml, entities) = parse("P and Q and R to S or T iff U").unwrap();
        assert_eq!(
            fml.display(&entities).to_string(),
            "((P ∧ Q ∧ R) → (S ∨ T)) ↔ U"
        );

        let (fml, entities) = parse("(P to Q) and (Q to P)").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "P ↔ Q");

        let (fml, entities) = parse("(P to Q) and (Q to R)").unwrap();
        assert_eq!(fml.display(&entities).to_string(), "(P → Q) ∧ (Q → R)");
    }
}
