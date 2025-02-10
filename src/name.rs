use crate::lang::{Formula, Sequent, SidedFormula, Term};
use regex::Regex;
use std::fmt;

/// A mapping between string names and their IDs.
/// This struct implements string interning for better performance,
/// enabling faster comparisons and memory efficiency.
#[derive(Clone, Debug, Default)]
pub struct Names {
    /// Vector of interned strings where index is used as the ID.
    /// This means the nth element corresponds to ID n.
    names: Vec<String>,
}

impl Names {
    /// The number of names.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Looks up the ID for a given name.
    /// If the name is not found, adds it and returns its new ID.
    pub fn get_id(&mut self, name: String) -> usize {
        self.names
            .iter()
            .position(|s| s == &name)
            .unwrap_or_else(|| {
                self.names.push(name);
                // return the last index
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
    pub fn get_name(&self, id: usize) -> String {
        self.names
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("?_{id}"))
    }

    fn get_name_ref(&self, id: usize) -> &str {
        self.names.get(id).unwrap()
    }

    /// Generates a fresh name and retrieves the ID associated with it.
    pub fn gen_fresh_id(&mut self, id: usize) -> usize {
        self.get_id(self.gen_fresh_name(self.get_name(id)))
    }
}

pub struct TermDisplay<'a> {
    term: &'a Term,
    names: &'a Names,
}

impl fmt::Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Term::*;
        match self.term {
            Var(id) => write!(f, "{}", self.names.get_name_ref(*id)),
            Func(id, ts) if ts.is_empty() => write!(f, "{}", self.names.get_name_ref(*id)),
            Func(id, ts) => {
                // write the function name followed by an opening bracket
                write!(f, "{}(", self.names.get_name_ref(*id))?;
                // iterate over the terms and display them
                for (i, t) in ts.iter().enumerate() {
                    // add comma before each term except the first one
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    // recursively display the term
                    write!(f, "{}", t.display(self.names))?;
                }
                // write the closing bracket
                write!(f, ")")
            }
        }
    }
}

impl Term {
    /// Returns a `TermDisplay` used to display the term with the given names.
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
            Pred(id, ts) if ts.is_empty() => write!(f, "{}", self.names.get_name_ref(*id))?,
            Pred(id, ts) => {
                write!(f, "{}(", self.names.get_name_ref(*id))?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{}", t.display(self.names))?;
                }
                write!(f, ")")?;
            }
            Not(p) => write!(f, r"\lnot {}", p.display_inner(self.names))?,
            And(l) if l.is_empty() => write!(f, r"\top")?,
            And(l) => {
                if self.is_inner {
                    write!(f, "(")?;
                }
                for (i, p) in l.iter().enumerate() {
                    if i > 0 {
                        write!(f, r" \land ")?;
                    }
                    write!(f, "{}", p.display_inner(self.names))?;
                }
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            Or(l) if l.is_empty() => write!(f, r"\bot")?,
            Or(l) => {
                if self.is_inner {
                    write!(f, "(")?;
                }
                for (i, p) in l.iter().enumerate() {
                    if i > 0 {
                        write!(f, r" \lor ")?;
                    }
                    write!(f, "{}", p.display_inner(self.names))?;
                }
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
                    r"{} \rightarrow {}",
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
                    r"{} \leftrightarrow {}",
                    p.display_inner(self.names),
                    q.display_inner(self.names)
                )?;
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            All(vs, p) => {
                for v in vs {
                    write!(f, r"\forall {}", self.names.get_name_ref(*v))?;
                }
                write!(f, "{}", p.display_inner(self.names))?;
            }
            Ex(vs, p) => {
                for v in vs.iter() {
                    write!(f, r"\exists {}", self.names.get_name(*v))?;
                }
                write!(f, "{}", p.display_inner(self.names))?;
            }
        }
        Ok(())
    }
}

impl Formula {
    /// Returns a `FormulaDisplay` used to display the formula with the given names.
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
    sequent: &'a Sequent<'a>,
    names: &'a Names,
}

impl fmt::Display for SequentDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, SidedFormula { fml, .. }) in self
            .sequent
            .iter()
            .filter(|p| p.is_antecedent())
            .enumerate()
        {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", fml.display(self.names))?;
        }
        write!(f, r" &\vdash ")?;
        for (i, SidedFormula { fml, .. }) in
            self.sequent.iter().filter(|p| p.is_succedent()).enumerate()
        {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", fml.display(self.names))?;
        }
        Ok(())
    }
}

impl SequentDisplay<'_> {
    // TODO: 2025/02/09 消す
    /// Returns the LaTeX representation of the sequent.
    pub fn _to_latex(&self) -> String {
        _to_latex(&self.to_string())
    }
}

impl<'a> Sequent<'a> {
    /// Returns a `SequentDisplay` used to display the sequent with the given names.
    pub fn display(&'a self, names: &'a Names) -> SequentDisplay<'a> {
        SequentDisplay {
            sequent: self,
            names,
        }
    }
}

// TODO: 2025/02/09 消す
fn _to_latex(s: &str) -> String {
    let s = s
        .replace("⊤", r"\top")
        .replace("⊥", r"\bot")
        .replace('¬', r"\lnot ")
        .replace('∧', r"\land")
        .replace('∨', r"\lor")
        .replace('→', r"\rightarrow")
        .replace('↔', r"\leftrightarrow")
        .replace('∀', r"\forall ")
        .replace('∃', r"\exists ")
        .replace('⊢', r"&\vdash")
        .replace('_', r"\_");

    Regex::new(r"v\\_(\d+)")
        .unwrap()
        .replace_all(&s, "v_{$1}")
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{parse_formula, parse_sequent, parse_term};
    use test_case::case;

    #[case("x")]
    #[case("f(x)")]
    #[case("f(x,y,z)")]
    #[case("f(x,g(y,h(x,z)))")]
    fn term_display(s: &str) {
        let mut names = Names::default();
        let term = parse_term(s, &mut names).unwrap();
        assert_eq!(term.display(&names).to_string(), s);
    }

    #[case("P(x)")]
    #[case("P(x,y,z)")]
    #[case("P(x,f(y,g(z)))")]
    #[case("¬P")]
    #[case("P1 ∧ Q ∧ R ∧ S")]
    #[case("P2 ∨ Q ∨ R ∨ S")]
    #[case("P3 → (Q → (R → S))")]
    #[case("P4 ↔ (Q ↔ (R ↔ S))")]
    #[case("∀xP(x)")]
    #[case("∀x∀y∀zP(x,y,z)")]
    #[case("∃xQ(x)")]
    #[case("∃x∃y∃zQ(x,y,z)")]
    #[case("((P ∧ Q ∧ R) → ((S ∨ T ∨ U) → V)) ↔ W")]
    fn fml_display(s: &str) {
        let mut names = Names::default();
        let fml = parse_formula(s, &mut names, true).unwrap();
        assert_eq!(fml.display(&names).to_string(), s);
    }

    #[case("P ⊢ Q")]
    #[case("P, Q, R ⊢ S, T, U")]
    #[case(" ⊢ ")]
    fn sequent_display(s: &str) {
        let mut names = Names::default();
        let seq = parse_sequent(s, &mut names, true, false).unwrap();
        // assert_eq!(seq.to_seq().display(&names).to_string(), s);
    }
}
