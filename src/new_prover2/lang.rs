use crate::lang::{Formula, Formula::*, Sequent};
use indexmap::IndexSet;
use rustc_hash::FxHasher;
use std::cell::OnceCell;
use std::hash::BuildHasherDefault;
use std::{fs, io};

type FxIndexSet<T> = IndexSet<T, BuildHasherDefault<FxHasher>>;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Side {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Cost {
    Prop(usize),
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

#[derive(Clone, Debug)]
pub(super) struct SequentWithArity<'a> {
    pub(super) seq: SequentExtended<'a>,
    pub(super) tactic: OnceCell<(usize, String)>,
    pub(super) processed_children_cnt: usize,
    pub(super) parent_idx: Option<usize>,
}

pub(super) struct Info<'a> {
    pub(super) file: &'a mut io::BufWriter<fs::File>,
}

impl Side {
    #[inline(always)]
    pub(super) fn opposite(self) -> Self {
        use Side::*;
        match self {
            Left => Right,
            Right => Left,
        }
    }
}

impl Formula {
    #[inline(always)]
    pub(super) fn extended(&self, side: Side) -> FormulaExtended {
        FormulaExtended { fml: self, side }
    }
}

impl<'a> FormulaExtended<'a> {
    #[inline(always)]
    fn get_cost(&self) -> Cost {
        use Cost::*;
        use Side::*;
        match (self.fml, self.side) {
            (Pred(..), _) => Atom,
            (And(_) | Ex(..), Left) | (Or(_) | To(..) | All(..), Right) | (Not(_), _) => Prop(1),
            (To(..), Left) | (Iff(..), _) => Prop(2),
            (And(l), Right) | (Or(l), Left) => Prop(l.len()),
            (All(..), Left) | (Ex(..), Right) => Quant,
        }
    }
    #[inline(always)]
    pub(super) fn opposite(&self) -> Self {
        self.fml.extended(self.side.opposite())
    }
    #[inline(always)]
    pub(super) fn is_atom(&self) -> bool {
        self.fml.is_atom()
    }
    #[inline(always)]
    pub(super) fn get_label(&self) -> String {
        let FormulaExtended { fml, side } = self;
        let fml_type = match fml {
            Not(_) => r"$\lnot$",
            And(l) => match l.as_slice() {
                [] => r"$\top$",
                _ => r"$\land$",
            },
            Or(l) => match l.as_slice() {
                [] => r"$\bot$",
                _ => r"$\lor$",
            },
            To(..) => r"$\rightarrow$",
            Iff(..) => r"$\leftrightarrow$",
            All(..) => r"$\forall$",
            Ex(..) => r"$\exists$",
            Pred(..) => unreachable!(),
        };
        format!("{fml_type}: {side:?}")
    }
}

impl<'a> SequentExtended<'a> {
    pub(super) fn to_seq(&self) -> Sequent<'a> {
        use Side::*;
        let mut ant = Vec::with_capacity(self.seq.len());
        let mut suc = Vec::with_capacity(self.seq.len());
        for FormulaExtended { fml, side } in &self.seq {
            match side {
                Left => ant.push(*fml),
                Right => suc.push(*fml),
            }
        }
        Sequent { ant, suc }
    }

    #[inline(always)]
    pub(super) fn push(&mut self, fml: FormulaExtended<'a>) {
        if self.seq.contains(&fml) {
            return;
        }
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

    #[inline(always)]
    pub(super) fn is_trivial(&self, fml: FormulaExtended<'a>) -> bool {
        fml.is_atom() && self.contains(&fml.opposite())
    }

    #[inline(always)]
    pub(super) fn into_sequent_with_arity(self, parent_idx: Option<usize>) -> SequentWithArity<'a> {
        SequentWithArity {
            seq: self,
            tactic: OnceCell::new(),
            processed_children_cnt: 0,
            parent_idx,
        }
    }
}
