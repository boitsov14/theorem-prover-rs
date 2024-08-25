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
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct FormulaExtended<'a> {
    pub(super) fml: &'a Formula,
    pub(super) side: Side,
}

#[derive(Clone, Debug, Default)]
pub(super) struct SequentExtended<'a> {
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
    #[inline(always)]
    pub(super) fn init(fml: &'a Formula, side: Side) -> Self {
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
    #[inline(always)]
    pub(super) fn opposite(&self) -> Self {
        Self::init(self.fml, self.side.opposite())
    }
}

impl<'a> SequentExtended<'a> {
    pub(super) fn init(ant: &'a [Formula], suc: &'a [Formula]) -> Self {
        let mut seq = Self::default();
        for fml in ant {
            seq.push(FormulaExtended::init(fml, Side::Left));
        }
        for fml in suc {
            seq.push(FormulaExtended::init(fml, Side::Right));
        }
        seq
    }

    #[inline(always)]
    pub(super) fn push(&mut self, fml: FormulaExtended<'a>) {
        // TODO: 2024/08/25 costを最初に定義することのパフォーマンスへの影響考察
        let cost = fml.get_cost();
        let i = self
            .seq
            .iter()
            .rposition(|p| p.get_cost() >= cost)
            .map_or(0, |x| x + 1);
        self.seq.shift_insert(i, fml);
    }

    #[inline(always)]
    pub(super) fn pop(&mut self) -> Option<FormulaExtended<'a>> {
        self.seq.pop()
    }

    #[inline(always)]
    pub(super) fn contains(&self, fml: &FormulaExtended<'a>) -> bool {
        self.seq.contains(fml)
    }
}
