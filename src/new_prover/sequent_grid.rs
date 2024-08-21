use crate::lang::Formula;
use crate::new_prover::lang::{
    Cost, FormulaExtended, SequentIdx,
    Side::{Left, Right},
};

/// Grid of sequents
pub(super) struct SequentGrid<'a> {
    pub(super) grid: Vec<FormulaExtended<'a>>,
    pub(super) idxs: Vec<SequentIdx>,
}

impl<'a> SequentGrid<'a> {
    fn init(ant: &'a [Formula], suc: &'a [Formula]) -> Self {
        let mut grid = Self {
            grid: vec![],
            idxs: vec![SequentIdx::new()],
        };
        for fml in ant {
            grid.push_fml(FormulaExtended::new(fml, Left));
        }
        for fml in suc {
            grid.push_fml(FormulaExtended::new(fml, Right));
        }
        grid
    }

    pub(super) fn len(&self) -> usize {
        self.grid.len()
    }

    pub(super) fn last_seq(&self) -> Option<&[FormulaExtended<'a>]> {
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

    pub(super) fn last_atom(&self) -> Option<&[FormulaExtended<'a>]> {
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

    pub(super) fn push_fml(&mut self, fml: FormulaExtended<'a>) {
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

    pub(super) fn pop_fml(&mut self) -> Option<FormulaExtended<'a>> {
        use crate::new_prover::lang::Cost::*;
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

    pub(super) fn drop_last_seq(&mut self) {
        let idx = self.idxs.pop().unwrap();
        self.grid.truncate(idx.start);
    }
}
