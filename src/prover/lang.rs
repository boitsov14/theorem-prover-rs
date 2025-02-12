use crate::lang::{
    Cost::{self, *},
    Formula::{self, *},
    Sequent,
    Side::{self, Left, Right},
    SidedFormula, SplitSequent,
};
use std::{cell::OnceCell, fmt};

#[derive(Clone, Debug)]
pub enum Tactic {
    Axiom,
    Not { side: Side },
    And { side: Side, children_cnt: usize },
    Or { side: Side, children_cnt: usize },
    To { side: Side },
    Iff { side: Side },
    All { side: Side },
    Ex { side: Side },
    // TODO: 2025/02/12 Add Comment why
    True,
    False,
}

impl Tactic {
    #[inline(always)]
    pub fn children_cnt(&self) -> usize {
        use Tactic::*;
        match self {
            Axiom => 0,
            Not { .. } => 1,
            And { children_cnt, .. } => *children_cnt,
            Or { children_cnt, .. } => *children_cnt,
            To { .. } => 2,
            Iff { .. } => 2,
            All { .. } => 1,
            Ex { .. } => 1,
            True => 0,
            False => 0,
        }
    }
}

impl fmt::Display for Tactic {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Tactic::*;
        match self {
            Axiom => write!(f, "Axiom"),
            Not { side } => write!(f, r"$\lnot$: {side}"),
            And { side, .. } => write!(f, r"$\land$: {side}"),
            Or { side, .. } => write!(f, r"$\lor$: {side}"),
            To { side } => write!(f, r"$\rightarrow$: {side}"),
            Iff { side } => write!(f, r"$\leftrightarrow$: {side}"),
            All { side } => write!(f, r"$\forall$: {side}"),
            Ex { side } => write!(f, r"$\exists$: {side}"),
            True => write!(f, r"$\top$: {Right}"),
            False => write!(f, r"$\bot$: {Left}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SequentExtendedLatex<'a> {
    pub seq: Sequent<'a>,
    pub tactic: OnceCell<(usize, String)>,
    pub processed_children_cnt: usize,
    pub parent_idx: Option<usize>,
}

impl Side {
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
    pub fn extended(&self, side: Side) -> SidedFormula {
        SidedFormula { fml: self, side }
    }
    #[inline(always)]
    pub fn get_label(&self, side: Side) -> String {
        let fml = match self {
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
        format!("{fml}: {side:?}")
    }
}

impl<'a> SidedFormula<'a> {
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
    #[inline(always)]
    pub fn opposite(&self) -> Self {
        self.fml.extended(self.side.opposite())
    }
    #[inline(always)]
    pub fn is_atom(&self) -> bool {
        self.fml.is_atom()
    }
}

impl<'a> SplitSequent<'a> {
    /// Convert Sequent to SequentExtended.
    /// Returns `None` if the Sequent is trivial.
    pub fn extended(&self) -> Option<Sequent> {
        let mut seq = Sequent::default();
        for fml in &self.ant {
            let fml = fml.extended(Left);
            if seq.is_trivial(fml) {
                return None;
            }
            seq.push(fml);
        }
        for fml in &self.suc {
            let fml = fml.extended(Right);
            if seq.is_trivial(fml) {
                return None;
            }
            seq.push(fml);
        }
        Some(seq)
    }
}

impl<'a> Sequent<'a> {
    pub fn to_seq(&self) -> SplitSequent<'a> {
        let mut ant = Vec::with_capacity(self.seq.len());
        let mut suc = Vec::with_capacity(self.seq.len());
        for SidedFormula { fml, side } in &self.seq {
            match side {
                Left => ant.push(*fml),
                Right => suc.push(*fml),
            }
        }
        SplitSequent { ant, suc }
    }

    #[inline(always)]
    pub fn push(&mut self, fml: SidedFormula<'a>) {
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
    pub fn pop(&mut self) -> Option<SidedFormula<'a>> {
        self.seq.pop()
    }

    #[inline(always)]
    pub fn last(&self) -> Option<&SidedFormula<'a>> {
        self.seq.last()
    }

    #[inline(always)]
    pub fn contains(&self, fml: &SidedFormula<'a>) -> bool {
        self.seq.contains(fml)
    }

    #[inline(always)]
    pub fn is_trivial(&self, fml: SidedFormula<'a>) -> bool {
        fml.is_atom() && self.contains(&fml.opposite())
    }

    #[inline(always)]
    pub fn is_trivial2(&self, fml1: SidedFormula<'a>, fml2: SidedFormula<'a>) -> bool {
        if (fml1.is_atom() && self.contains(&fml1.opposite()))
            || (fml2.is_atom() && self.contains(&fml2.opposite()))
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

    #[inline(always)]
    pub fn extended_latex(self, parent_idx: Option<usize>) -> SequentExtendedLatex<'a> {
        SequentExtendedLatex {
            seq: self,
            tactic: OnceCell::new(),
            processed_children_cnt: 0,
            parent_idx,
        }
    }
}
