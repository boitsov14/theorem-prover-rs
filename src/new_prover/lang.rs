use crate::lang::{Formula, FALSE, TRUE};
use itertools::Itertools;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Side {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Cost {
    Alpha,
    Beta(usize),
    Quant,
    Redundant,
    Atom,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct FormulaExtended<'a> {
    fml: &'a Formula,
    side: Side,
    cost: Cost,
}

struct SequentExtended<'a> {
    seq: Vec<FormulaExtended<'a>>,
    finished: bool,
}

impl Formula {
    fn get_cost(&self, side: Side) -> Cost {
        use Cost::*;
        use Formula::*;
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

impl<'a> FormulaExtended<'a> {
    fn new(fml: &'a Formula, side: Side) -> Self {
        Self {
            fml,
            side,
            cost: fml.get_cost(side),
        }
    }
}

impl<'a> SequentExtended<'a> {
    fn new(ant: &'a [Formula], suc: &'a [Formula]) -> Self {
        let mut seq = Self {
            seq: Vec::with_capacity(ant.len() + suc.len()),
            finished: false,
        };
        for fml in ant.iter().rev() {
            seq.push(FormulaExtended::new(fml, Side::Left));
        }
        for fml in suc.iter().rev() {
            seq.push(FormulaExtended::new(fml, Side::Right));
        }
        seq
    }

    fn push(&mut self, fml: FormulaExtended<'a>) {
        if self
            .seq
            .iter()
            .any(|p| p.fml == fml.fml && p.side != fml.side)
        {
            self.finished = true;
        }

        if (*fml.fml == TRUE && fml.side == Side::Right)
            || (*fml.fml == FALSE && fml.side == Side::Left)
        {
            self.finished = true;
        }

        let i = self
            .seq
            .iter()
            .rposition(|p| p.cost >= fml.cost)
            .map_or(0, |x| x + 1);
        self.seq.insert(i, fml);
    }

    fn pop(&mut self) -> Option<FormulaExtended<'a>> {
        use Cost::*;
        use Formula::*;
        use Side::*;
        let fml = self.seq.last()?;
        match fml.cost {
            Quant | Redundant | Atom => {
                return None;
            }
            _ => {}
        }
        let mut fml = self.seq.pop()?;
        match (fml.fml, fml.side) {
            (And(l), Right) => {
                if self
                    .seq
                    .iter()
                    .any(|p| p.side == Right && l.iter().contains(p.fml))
                {
                    fml.cost = Redundant;
                    self.push(fml);
                    return self.pop();
                }
            }
            (Or(l), Left) => {
                if self
                    .seq
                    .iter()
                    .any(|p| p.side == Left && l.iter().contains(p.fml))
                {
                    fml.cost = Redundant;
                    self.push(fml);
                    return self.pop();
                }
            }
            (To(p, q), Left) => {}
            (Iff(p, q), Left) => {}
            (Iff(p, q), Right) => {}
            _ => {}
        }
        Some(fml)
    }
}
