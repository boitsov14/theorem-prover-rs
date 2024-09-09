use crate::lang::{Formula, Formula::*};

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

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct FormulaExtended<'a> {
    pub(super) fml: &'a Formula,
    pub(super) side: Side,
    pub(super) cost: Cost,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct SequentIdx {
    pub(super) start: usize,
    pub(super) redundant: usize,
    pub(super) quant: usize,
    pub(super) atom: usize,
    pub(super) beta: usize,
    pub(super) end: usize,
}

impl Formula {
    // TODO: 2024/08/21 cost不要ならproverへ移動
    #[inline(always)]
    fn get_cost(&self, side: Side) -> Cost {
        use Cost::*;
        use Side::*;
        match (self, side) {
            (Pred(..), _) => Atom,
            (And(_) | Ex(..), Left) | (Or(_) | To(..) | All(..), Right) | (Not(_), _) => Alpha,
            (To(..), Left) | (Iff(..), _) => Beta(2),
            (And(l), Right) | (Or(l), Left) => Beta(l.len()),
            (All(..), Left) | (Ex(..), Right) => Quant,
        }
    }
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

impl SequentIdx {
    pub(super) fn new() -> Self {
        Self {
            start: 0,
            redundant: 0,
            quant: 0,
            atom: 0,
            beta: 0,
            end: 0,
        }
    }

    fn init(start: usize) -> Self {
        Self {
            start,
            redundant: start,
            quant: start,
            atom: start,
            beta: start,
            end: start,
        }
    }

    #[inline]
    pub(super) fn add_all(&mut self, n: usize) {
        self.start += n;
        self.redundant += n;
        self.quant += n;
        self.atom += n;
        self.beta += n;
        self.end += n;
    }
}

impl<'a> FormulaExtended<'a> {
    #[inline]
    pub(super) fn new(fml: &'a Formula, side: Side) -> Self {
        Self {
            fml,
            side,
            cost: fml.get_cost(side),
        }
    }
}
