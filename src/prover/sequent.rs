use crate::{
    intern::{Names, to_unicode},
    lang::{
        Formula::{self, *},
        SplitSequent,
    },
};
use Cost::*;
use Side::*;
use indexmap::IndexSet;
use rustc_hash::{FxHashSet, FxHasher};
use std::{fmt, hash::BuildHasherDefault};

type FxIndexSet<T> = IndexSet<T, BuildHasherDefault<FxHasher>>;

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

// TODO: 2025/05/22 atomやquantを分けるなら不要？
/// cost for propositional proof operations (ordered by priority)
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Cost {
    // lower cost for fewer branches
    Prop(usize),
    // cannot be further simplified
    Atom,
    // deferred because cost is used only for proving propositional logic
    Quant,
}

/// formula with side (left/right) in a sequent
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SidedFormula<'a> {
    pub fml: &'a Formula,
    pub side: Side,
}

/// sequent with an index set of sided formulas
#[derive(Clone, Debug, Default)]
pub struct Sequent<'a> {
    /// index set of sided formulas
    // TODO: 2025/05/22 名前要検討
    seq: FxIndexSet<SidedFormula<'a>>,
    atoms: FxHashSet<SidedFormula<'a>>,
    // TODO: 2025/05/22 要検討
    // quant: FxIndexSet<SidedFormula<'a>>,
    // quant: Vec<SidedFormula<'a>>,
}

impl Side {
    #[must_use]
    #[inline(always)]
    pub fn opposite(self) -> Self {
        match self {
            Left => Right,
            Right => Left,
        }
    }
}

impl Formula {
    #[inline(always)]
    pub fn with_side(&self, side: Side) -> SidedFormula {
        SidedFormula { fml: self, side }
    }
}

impl SidedFormula<'_> {
    #[inline(always)]
    fn get_cost(&self) -> Cost {
        match (self.fml, self.side) {
            (Pred(..), _) => Atom,
            (And(_) | Ex(..), Left) | (Or(_) | To(..) | All(..), Right) | (Not(_), _) => Prop(1),
            (To(..), Left) | (Iff(..), _) => Prop(2),
            (And(l), Right) | (Or(l), Left) => Prop(l.len()),
            (All(..), Left) | (Ex(..), Right) => Quant,
        }
    }

    #[must_use]
    #[inline(always)]
    fn opposite(&self) -> Self {
        self.fml.with_side(self.side.opposite())
    }

    #[inline(always)]
    pub fn is_atom(&self) -> bool {
        self.fml.is_atom()
    }
}

impl<'a> Sequent<'a> {
    pub fn init(SplitSequent { ant, suc }: &'a SplitSequent) -> Self {
        let mut seq = Self::default();
        for fml in ant {
            seq.push(fml.with_side(Left));
        }
        for fml in suc {
            seq.push(fml.with_side(Right));
        }
        seq
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
            let cost = fml.get_cost();
            let i = self.seq.partition_point(|p| p.get_cost() >= cost);
            self.seq.insert_before(i, fml);
        }
    }

    #[inline(always)]
    pub fn pop(&mut self) -> Option<SidedFormula<'a>> {
        self.seq.pop()
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
        if (fml1.is_atom() && self.contains_atom(&fml1.opposite())) || (fml2.is_atom() && self.contains_atom(&fml2.opposite())) {
            // trivial if either of them is trivial
            return true;
        }
        let SidedFormula { fml: fml1, side: side1 } = fml1;
        let SidedFormula { fml: fml2, side: side2 } = fml2;
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
        for (i, SidedFormula { fml, .. }) in self
            .seq
            .seq
            .iter()
            .chain(self.seq.atoms.iter())
            .filter(|p| p.side == Left)
            .enumerate()
        {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", fml.display(self.names))?;
        }
        write!(f, r" &\vdash ")?;
        for (i, SidedFormula { fml, .. }) in self
            .seq
            .seq
            .iter()
            .chain(self.seq.atoms.iter())
            .filter(|p| p.side == Right)
            .enumerate()
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
    }
}

impl<'a> Sequent<'a> {
    /// Returns a `SequentDisplay` used to display the sequent with the given names.
    pub fn display(&'a self, names: &'a Names) -> SequentDisplay<'a> {
        SequentDisplay { seq: self, names }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_sequent;
    use test_case::case;

    #[case("P ⊢ Q")]
    #[case("P, Q, R ⊢ S, T, U")]
    #[case(" ⊢ ")]
    fn sequent_display(s: &str) {
        let mut names = Names::default();
        let seq = parse_sequent(s, &mut names, true, false).unwrap();
        // assert_eq!(seq.to_seq().display(&names).to_string(), s);
    }
}
