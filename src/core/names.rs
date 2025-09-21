use crate::core::syntax::{
    Formula::{self, *},
    Term::{self, *},
};
use std::{fmt, ops::Index};

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

    // TODO: 2025/02/17 コメント修正
    // 必ず既存のIDが既に存在している場合にのみ使うようにする旨コメントを追加
    /// Generates a fresh name and retrieves the ID associated with it.
    /// Generates a fresh name by appending a single quote (') to the given name.
    pub fn gen_fresh_id(&mut self, id: usize) -> usize {
        let mut name = self[id].clone();
        while self.names.contains(&name) {
            name.push('\'');
        }
        self.get_id(name)
    }
}

impl Index<usize> for Names {
    type Output = String;

    fn index(&self, index: usize) -> &Self::Output {
        &self.names[index]
    }
}

pub struct TermDisplay<'a> {
    term: &'a Term,
    names: &'a Names,
}

impl fmt::Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.term {
            Var(id) => write!(f, "{}", self.names[*id]),
            Func(id, ts) if ts.is_empty() => write!(f, "{}", self.names[*id]),
            Func(id, ts) => {
                // write the function name followed by an opening bracket
                write!(f, "{}(", self.names[*id])?;
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
    pub const fn display<'a>(&'a self, names: &'a Names) -> TermDisplay<'a> {
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
        match self.formula {
            Pred(id, ts) if ts.is_empty() => write!(f, "{}", self.names[*id])?,
            Pred(id, ts) => {
                write!(f, "{}(", self.names[*id])?;
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
            Or(l) if l.is_empty() => write!(f, r"\lfalse")?,
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
                    r"{} \lif {}",
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
                    r"{} \liff {}",
                    p.display_inner(self.names),
                    q.display_inner(self.names)
                )?;
                if self.is_inner {
                    write!(f, ")")?;
                }
            }
            All(vs, p) => {
                for v in vs {
                    write!(f, r"\lall {}", self.names[*v])?;
                }
                write!(f, "{}", p.display_inner(self.names))?;
            }
            Ex(vs, p) => {
                for v in vs {
                    write!(f, r"\lis {}", self.names[*v])?;
                }
                write!(f, "{}", p.display_inner(self.names))?;
            }
        }
        Ok(())
    }
}

impl Formula {
    /// Returns a `FormulaDisplay` used to display the formula with the given names.
    pub const fn display<'a>(&'a self, names: &'a Names) -> FormulaDisplay<'a> {
        FormulaDisplay {
            formula: self,
            names,
            is_inner: false,
        }
    }

    const fn display_inner<'a>(&'a self, names: &'a Names) -> FormulaDisplay<'a> {
        FormulaDisplay {
            formula: self,
            names,
            is_inner: true,
        }
    }
}

impl FormulaDisplay<'_> {
    /// Returns the unicode representation of the formula
    /// by converting LaTeX commands to symbols
    pub fn to_unicode(&self) -> String {
        to_unicode(&self.to_string())
    }
}

/// Returns the unicode representation
/// by converting LaTeX commands to symbols
pub fn to_unicode(s: &str) -> String {
    s.replace(r"\top", "⊤")
        .replace(r"\lfalse", "⊥")
        .replace(r"\lnot ", "¬")
        .replace(r"\land", "∧")
        .replace(r"\lor", "∨")
        .replace(r"\liff", "↔")
        .replace(r"\lif", "→")
        .replace(r"\lall ", "∀")
        .replace(r"\lis ", "∃")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser::{parse_formula, parse_term};
    use std::fmt;
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
        assert_eq!(fml.display(&names).to_unicode(), s);
    }

    /// A writer that fails after n successful `write_str` calls.
    struct CountFail(usize);

    impl fmt::Write for CountFail {
        /// Fails after `n` successful `write_str` calls.
        fn write_str(&mut self, _s: &str) -> fmt::Result {
            let Self(ref mut i) = *self;
            if *i == 0 {
                return Err(fmt::Error);
            }
            *i -= 1;
            Ok(())
        }
    }

    #[test]
    fn term_display_error_branches_sweep() {
        // prepare a comprehensive term: parentheses, commas, nested terms
        let mut names = Names::default();
        let t = parse_term("f(x,g(y,h(x,z)),u,v,w)", &mut names).unwrap();

        // sweep CountFail over all write positions
        let mut i: usize = 0;
        loop {
            let mut w = CountFail(i);
            if fmt::write(&mut w, format_args!("{}", t.display(&names))).is_ok() {
                break;
            }
            i += 1;
        }
    }

    #[test]
    fn fml_display_error_branches_sweep() {
        // build a comprehensive formula that contains all operators/quantifiers
        let mut names = Names::default();
        let s = "((P ↔ (Q ↔ R)) ∧ (P → (Q → R)) ∧ (P → (Q ∧ R)) ∧ (P → (Q ∨ R)) ∧ ¬P ∧ (⊤ ∨ ⊤) ∧ ⊥ ∧ P ∧ ∀x∀y∀zP(x,f(y,g(z))) ∧ ∃u∃vQ(u,v))";
        let fml = parse_formula(s, &mut names, true).unwrap();

        // sweep CountFail over all write positions
        let mut i: usize = 0;
        loop {
            let mut w = CountFail(i);
            if fmt::write(&mut w, format_args!("{}", fml.display(&names))).is_ok() {
                break;
            }
            i += 1;
        }
    }
}
