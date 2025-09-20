use crate::core::{
    names::{Names, to_unicode},
    syntax::{
        Formula::{self, *},
        SplitSequent,
    },
};
use Side::*;
use rustc_hash::FxHashSet;
use std::fmt;

/// side in sequent calculus: antecedent ⊢ succedent
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Side {
    /// antecedent
    Left,
    /// succedent
    Right,
}

impl fmt::Display for Side {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Left => write!(f, "Left"),
            Right => write!(f, "Right"),
        }
    }
}

/// formula with side (left/right) in a sequent
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SidedFormula<'a> {
    pub fml: &'a Formula,
    pub side: Side,
}

#[derive(Clone, Debug, Default)]
pub struct Sequent<'a> {
    // single branch formulas (cost 1)
    single: Vec<SidedFormula<'a>>,
    // Multi-branch formulas (cost 2+)
    multi: Vec<SidedFormula<'a>>,
    // atoms
    atoms: FxHashSet<SidedFormula<'a>>,
}

impl Side {
    #[must_use]
    #[inline(always)]
    pub const fn opposite(self) -> Self {
        match self {
            Left => Right,
            Right => Left,
        }
    }
}

impl Formula {
    #[inline(always)]
    pub const fn with_side(&'_ self, side: Side) -> SidedFormula<'_> {
        SidedFormula { fml: self, side }
    }
}

impl SidedFormula<'_> {
    #[inline(always)]
    fn get_cost(&self) -> usize {
        match (self.fml, self.side) {
            (And(_) | Ex(..), Left) | (Or(_) | To(..) | All(..), Right) | (Not(_), _) => 1,
            (To(..), Left) | (Iff(..), _) => 2,
            (And(l), Right) | (Or(l), Left) => l.len(),
            (Pred(..), _) | (All(..), Left) | (Ex(..), Right) => unreachable!(),
        }
    }

    #[must_use]
    #[inline(always)]
    const fn opposite(&self) -> Self {
        self.fml.with_side(self.side.opposite())
    }

    #[inline(always)]
    pub const fn is_atom(&self) -> bool {
        self.fml.is_atom()
    }
}

impl<'a> Sequent<'a> {
    pub fn new(SplitSequent { ant, suc }: &'a SplitSequent) -> Self {
        let mut seq = Self::default();
        for fml in ant {
            seq.push(fml.with_side(Left));
        }
        for fml in suc {
            seq.push(fml.with_side(Right));
        }
        seq
    }

    /// iterate over all formulas in the sequent
    pub fn iter(&self) -> impl Iterator<Item = &SidedFormula<'a>> {
        self.single
            .iter()
            .chain(self.multi.iter())
            .chain(self.atoms.iter())
    }

    pub fn is_initially_trivial(&self) -> bool {
        self.atoms
            .iter()
            .any(|fml| self.contains_atom(&fml.opposite()))
    }

    #[inline(always)]
    pub fn push(&mut self, fml: SidedFormula<'a>) {
        if fml.is_atom() {
            self.atoms.insert(fml);
        } else {
            match fml.get_cost() {
                0 | 1 => self.single.push(fml),
                _ => self.multi.push(fml),
            }
        }
    }

    /// Pop minimum cost formula efficiently
    pub fn pop(&mut self) -> Option<SidedFormula<'a>> {
        // Check buckets in cost order
        self.single.pop().or_else(|| self.multi.pop())
    }

    #[inline(always)]
    pub fn contains_atom(&self, fml: &SidedFormula<'a>) -> bool {
        self.atoms.contains(fml)
    }

    #[inline(always)]
    pub fn is_trivial(&self, fml: SidedFormula<'a>) -> bool {
        fml.is_atom() && self.contains_atom(&fml.opposite())
    }

    #[inline(always)]
    pub fn is_trivial2(&self, fml1: SidedFormula<'a>, fml2: SidedFormula<'a>) -> bool {
        if (fml1.is_atom() && self.contains_atom(&fml1.opposite()))
            || (fml2.is_atom() && self.contains_atom(&fml2.opposite()))
        {
            // trivial if either of them is trivial
            return true;
        }
        let SidedFormula {
            fml: fml1,
            side: side1,
        } = fml1;
        let SidedFormula {
            fml: fml2,
            side: side2,
        } = fml2;
        // trivial if same formula with different side
        fml1 == fml2 && side1 != side2
    }
}

pub struct SequentDisplay<'a> {
    seq: &'a Sequent<'a>,
    names: &'a Names,
}

impl fmt::Display for SequentDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, SidedFormula { fml, .. }) in self.seq.iter().filter(|p| p.side == Left).enumerate()
        {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", fml.display(self.names))?;
        }
        write!(f, r" \vdash ")?;
        for (i, SidedFormula { fml, .. }) in self.seq.iter().filter(|p| p.side == Right).enumerate()
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
    /// Returns the unicode representation of the sequent
    /// by converting LaTeX commands to symbols
    pub fn to_unicode(&self) -> String {
        to_unicode(&self.to_string())
            .replace(r"\vdash", "⊢")
            .trim()
            .into()
    }
}

impl<'a> Sequent<'a> {
    /// Returns a `SequentDisplay` used to display the sequent with the given names.
    pub const fn display(&'a self, names: &'a Names) -> SequentDisplay<'a> {
        SequentDisplay { seq: self, names }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser::parse_sequent;
    use std::fmt;
    use test_case::case;

    #[case("P ⊢ Q" => "P ⊢ Q")]
    #[case("⊢" => "⊢")]
    #[case("P, Q, R ⊢ S, T, U" => "P, R, Q ⊢ U, T, S")]
    #[case("⊢ P" => "⊢ P")]
    #[case("Q ⊢" => "Q ⊢")]
    #[case("P ∧ Q ⊢ R ∨ S" => "P ∧ Q ⊢ R ∨ S")]
    #[case("P → Q, Q → R ⊢ P → R" => "P → Q, Q → R ⊢ P → R")]
    // TODO: 2025/09/19 あとで有効化
    // #[case("∀x P(x) ⊢ ∃y Q(y)" => "∀x P(x) ⊢ ∃y Q(y)")]
    // #[case("∀x,y P(x,y), ∃z,w Q(z,w) ⊢ ∃z,w Q(z,w), ∀x,y P(x,y)" => "∀x,y P(x,y), ∃z,w Q(z,w) ⊢ ∃z,w Q(z,w), ∀x,y P(x,y)")]
    fn sequent_display(s: &str) -> String {
        let mut names = Names::default();
        let seq = parse_sequent(s, &mut names, true, false).unwrap();
        let seq = Sequent::new(&seq);
        seq.display(&names).to_unicode()
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
    fn sequent_display_error_branches_sweep() {
        let mut names = Names::default();
        let s = "P, Q ⊢ R, S";
        let split = parse_sequent(s, &mut names, true, false).unwrap();
        let seq = Sequent::new(&split);

        // sweep CountFail over all write positions
        let mut i: usize = 0;
        loop {
            let mut w = CountFail(i);
            if fmt::write(&mut w, format_args!("{}", seq.display(&names))).is_ok() {
                break;
            }
            i += 1;
        }
    }
}
