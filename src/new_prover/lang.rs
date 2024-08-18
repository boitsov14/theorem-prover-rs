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
    Atom,
    Quant,
    Redundant,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct FormulaExtended<'a> {
    fml: &'a Formula,
    side: Side,
    cost: Cost,
}

struct SequentIdx {
    start: usize,
    redundant: usize,
    quant: usize,
    atom: usize,
    beta: usize,
}

struct SequentTable<'a> {
    seqs: Vec<FormulaExtended<'a>>,
    idxs: Vec<SequentIdx>,
}

// TODO: 2024/08/17 あとで消す
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

impl SequentIdx {
    fn init(table: &SequentTable) -> Self {
        Self {
            start: table.seqs.len(),
            redundant: 0,
            quant: 0,
            atom: 0,
            beta: 0,
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

impl<'a> SequentTable<'a> {
    fn init(ant: &'a [Formula], suc: &'a [Formula]) -> Self {
        let mut table = Self {
            seqs: vec![],
            idxs: vec![],
        };
        let mut idx = SequentIdx::init(&table);
        for fml in ant {
            table.push_fml(FormulaExtended::new(fml, Side::Left), &mut idx);
        }
        for fml in suc {
            table.push_fml(FormulaExtended::new(fml, Side::Right), &mut idx);
        }
        table.idxs.push(idx);
        table
    }

    fn push_fml(&mut self, fml: FormulaExtended<'a>, idx: &mut SequentIdx) {
        use Cost::*;
        match fml.cost {
            Alpha => self.seqs.push(fml),
            Beta(_) => {
                let i = self.seqs[idx.start + idx.atom..idx.start + idx.beta]
                    .iter()
                    .rposition(|p| p.cost >= fml.cost)
                    .map_or(0, |x| x + 1);
                self.seqs.insert(idx.start + idx.beta + i, fml);
                idx.beta += 1;
            }
            Atom => {
                self.seqs.insert(idx.start + idx.atom, fml);
                idx.atom += 1;
                idx.beta += 1;
            }
            Quant => {
                self.seqs.insert(idx.start + idx.quant, fml);
                idx.quant += 1;
                idx.atom += 1;
                idx.beta += 1;
            }
            Redundant => {
                self.seqs.insert(idx.start + idx.redundant, fml);
                idx.redundant += 1;
                idx.quant += 1;
                idx.atom += 1;
                idx.beta += 1;
            }
        }
    }
}

// TODO: 2024/08/17 あとで消す
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
