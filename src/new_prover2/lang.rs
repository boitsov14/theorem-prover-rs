use crate::lang::{Formula, Formula::*};
use indexmap::IndexSet;
use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

type FxIndexSet<T> = IndexSet<T, BuildHasherDefault<FxHasher>>;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Side {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Cost {
    Alpha,
    Beta(usize),
    Atom,
    Quant,
    Redundant,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FormulaExtended<'a> {
    pub(super) fml: &'a Formula,
    pub(super) side: Side,
}

#[derive(Clone, Debug, Default)]
struct SequentExtended<'a> {
    seq: FxIndexSet<FormulaExtended<'a>>,
}

impl Side {
    pub(super) fn opposite(self) -> Self {
        use Side::*;
        match self {
            Left => Right,
            Right => Left,
        }
    }
}

impl<'a> FormulaExtended<'a> {
    #[inline]
    pub(super) fn new(fml: &'a Formula, side: Side) -> Self {
        Self { fml, side }
    }
    #[inline(always)]
    fn get_cost(&self) -> Cost {
        use Cost::*;
        use Side::*;
        match (self.fml, self.side) {
            (Pred(..), _) => Atom,
            (And(_) | Ex(..), Left) | (Or(_) | To(..) | All(..), Right) | (Not(_), _) => Alpha,
            (To(..), Left) | (Iff(..), _) => Beta(2),
            (And(l), Right) | (Or(l), Left) => Beta(l.len()),
            (All(..), Left) | (Ex(..), Right) => Quant,
        }
    }
}

impl<'a> SequentExtended<'a> {
    pub(super) fn init(ant: &'a [Formula], suc: &'a [Formula]) -> Self {
        let mut seq = Self::default();
        // TODO: 2024/08/25
        seq
    }
    #[inline(always)]
    pub(super) fn push_fml(&mut self, fml: FormulaExtended<'a>) {
        let i = self
            .seq
            .iter()
            .rposition(|p| p.get_cost() >= fml.get_cost())
            .map_or(0, |x| x + 1);
        // TODO: 2024/08/25
    }
}
