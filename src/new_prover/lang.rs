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

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct FormulaExtended<'a> {
    fml: &'a Formula,
    side: Side,
    cost: Cost,
}

#[derive(Clone, Copy, Debug)]
struct SequentIdx {
    start: usize,
    redundant: usize,
    quant: usize,
    atom: usize,
    beta: usize,
}

/// Grid of sequents
struct SequentGrid<'a> {
    grid: Vec<FormulaExtended<'a>>,
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

impl Side {
    fn opposite(self) -> Self {
        use Side::*;
        match self {
            Left => Right,
            Right => Left,
        }
    }
}

impl SequentIdx {
    fn new() -> Self {
        Self {
            start: 0,
            redundant: 0,
            quant: 0,
            atom: 0,
            beta: 0,
        }
    }

    fn init(grid: &SequentGrid) -> Self {
        Self {
            start: grid.grid.len(),
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

impl<'a> SequentGrid<'a> {
    fn init(ant: &'a [Formula], suc: &'a [Formula]) -> Self {
        let mut grid = Self {
            grid: vec![],
            idxs: vec![SequentIdx::new()],
        };
        for fml in ant {
            grid.push_fml(FormulaExtended::new(fml, Side::Left));
        }
        for fml in suc {
            grid.push_fml(FormulaExtended::new(fml, Side::Right));
        }
        grid
    }

    fn last_seq(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.start..])
    }

    fn last_redundant(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.start..idx.start + idx.redundant])
    }

    fn last_quant(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.start + idx.redundant..idx.start + idx.quant])
    }

    fn last_atom(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.start + idx.quant..idx.start + idx.atom])
    }

    fn last_beta(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.start + idx.atom..idx.start + idx.beta])
    }

    fn last_alpha(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.start + idx.beta..])
    }

    fn is_trivial(&self, fml: FormulaExtended<'a>) -> bool {
        (*fml.fml == TRUE && fml.side == Side::Right)
            || (*fml.fml == FALSE && fml.side == Side::Left)
            || (fml.fml.is_atom()
                && self
                    .last_atom()
                    .unwrap()
                    .iter()
                    .any(|p| p.fml == fml.fml && p.side != fml.side))
    }

    fn push_fml(&mut self, fml: FormulaExtended<'a>) {
        use Cost::*;
        match fml.cost {
            Alpha => self.grid.push(fml),
            Beta(_) => {
                let i = self
                    .last_beta()
                    .unwrap()
                    .iter()
                    .rposition(|p| p.cost >= fml.cost)
                    .map_or(0, |x| x + 1);
                self.grid.insert(
                    self.idxs.last().unwrap().start + self.idxs.last().unwrap().atom + i,
                    fml,
                );
                self.idxs.last_mut().unwrap().beta += 1;
            }
            Atom => {
                self.grid.insert(
                    self.idxs.last().unwrap().start + self.idxs.last().unwrap().atom,
                    fml,
                );
                self.idxs.last_mut().unwrap().atom += 1;
                self.idxs.last_mut().unwrap().beta += 1;
            }
            Quant => {
                self.grid.insert(
                    self.idxs.last().unwrap().start + self.idxs.last().unwrap().quant,
                    fml,
                );
                self.idxs.last_mut().unwrap().quant += 1;
                self.idxs.last_mut().unwrap().atom += 1;
                self.idxs.last_mut().unwrap().beta += 1;
            }
            Redundant => {
                self.grid.insert(
                    self.idxs.last().unwrap().start + self.idxs.last().unwrap().redundant,
                    fml,
                );
                self.idxs.last_mut().unwrap().redundant += 1;
                self.idxs.last_mut().unwrap().quant += 1;
                self.idxs.last_mut().unwrap().atom += 1;
                self.idxs.last_mut().unwrap().beta += 1;
            }
        }
    }

    fn pop_fml(&mut self) -> Option<FormulaExtended<'a>> {
        use Cost::*;
        let fml = self.grid.pop()?;
        match fml.cost {
            Alpha => {}
            Beta(_) => {
                self.idxs.last_mut()?.beta -= 1;
            }
            Atom => {
                self.idxs.last_mut()?.atom -= 1;
                self.idxs.last_mut()?.beta -= 1;
            }
            Quant => {
                self.idxs.last_mut()?.quant -= 1;
                self.idxs.last_mut()?.atom -= 1;
                self.idxs.last_mut()?.beta -= 1;
            }
            Redundant => {
                self.idxs.last_mut()?.redundant -= 1;
                self.idxs.last_mut()?.quant -= 1;
                self.idxs.last_mut()?.atom -= 1;
                self.idxs.last_mut()?.beta -= 1;
            }
        }
        Some(fml)
    }

    fn drop_last_seq(&mut self) {
        let idx = self.idxs.pop().unwrap();
        self.grid.truncate(idx.start);
    }

    fn prove_prop(&mut self) -> bool {
        use Formula::*;
        use Side::*;
        while let Some(fml) = self.pop_fml() {
            match (fml.fml, fml.side) {
                (Not(p), _) => {
                    // add the inner formula to the opposite side
                    let new_fml = FormulaExtended::new(p, fml.side.opposite());
                    if self.is_trivial(new_fml) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_fml);
                }
                (And(l), Left) | (Or(l), Right) => {
                    // add all formulas to the same side
                    for p in l {
                        let new_fml = FormulaExtended::new(p, fml.side);
                        if self.is_trivial(new_fml) {
                            self.drop_last_seq();
                            continue;
                        }
                        self.push_fml(new_fml);
                    }
                }
                (And(l), Right) => {
                    // TODO: 2024/08/20 costがなければもっとシンプルに書ける
                    // check if the formula is redundant
                    if l.iter().any(|p| {
                        self.last_seq()
                            .unwrap()
                            .iter()
                            .any(|q| q.fml == p && q.side == Right)
                    }) {
                        let mut fml = fml;
                        fml.cost = Cost::Redundant;
                        self.push_fml(fml);
                        continue;
                    }
                    todo!();
                }
                (Or(l), Left) => {}
                (To(p, q), Left) => {
                    // add the premise to the succedent side
                    let new_fml = FormulaExtended::new(p, Right);
                    if self.is_trivial(new_fml) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_fml);
                    // make a new sequent
                    let idx = self.idxs.last().unwrap();
                    for i in idx.start..self.grid.len() - 1 {
                        self.grid.push(self.grid[i]);
                    }
                    self.idxs.push(*idx);
                    // add the conclusion to the antecedent side
                    let new_fml = FormulaExtended::new(q, Left);
                    if self.is_trivial(new_fml) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_fml);
                }
                (To(p, q), Right) => {
                    // add the premise to the antecedent side
                    let new_fml = FormulaExtended::new(p, Left);
                    if self.is_trivial(new_fml) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_fml);
                    // add the conclusion to the succedent side
                    let new_fml = FormulaExtended::new(q, Right);
                    if self.is_trivial(new_fml) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_fml);
                }
                (Iff(p, q), Left) => {}
                (Iff(p, q), Right) => {}
                (Pred(_, _), _) => return false,
                (Ex(_, _) | All(_, _), _) => unimplemented!(),
            }
        }
        true
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
