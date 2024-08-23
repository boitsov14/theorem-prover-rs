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
    pub(super) fn init(ant: &'a [Formula], suc: &'a [Formula]) -> Self {
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
        Some(&self.grid[idx.start..idx.end])
    }

    fn last_redundant(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.start..idx.redundant])
    }

    fn last_quant(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.redundant..idx.quant])
    }

    pub(super) fn last_atom(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.quant..idx.atom])
    }

    fn last_beta(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.atom..idx.beta])
    }

    fn last_alpha(&self) -> Option<&[FormulaExtended<'a>]> {
        let idx = self.idxs.last()?;
        Some(&self.grid[idx.beta..idx.end])
    }

    pub(super) fn push_fml(&mut self, fml: FormulaExtended<'a>) {
        use Cost::*;
        match fml.cost {
            Alpha => {
                self.grid.insert(self.idxs.last().unwrap().end, fml);
                self.idxs.last_mut().unwrap().end += 1;
            }
            Beta(_) => {
                let i = self
                    .last_beta()
                    .unwrap()
                    .iter()
                    .rposition(|p| p.cost >= fml.cost)
                    .map_or(0, |x| x + 1);
                self.grid.insert(self.idxs.last().unwrap().atom + i, fml);
                self.idxs.last_mut().unwrap().beta += 1;
                self.idxs.last_mut().unwrap().end += 1;
            }
            Atom => {
                self.grid.insert(self.idxs.last().unwrap().atom, fml);
                self.idxs.last_mut().unwrap().atom += 1;
                self.idxs.last_mut().unwrap().beta += 1;
                self.idxs.last_mut().unwrap().end += 1;
            }
            Quant => {
                self.grid.insert(self.idxs.last().unwrap().quant, fml);
                self.idxs.last_mut().unwrap().quant += 1;
                self.idxs.last_mut().unwrap().atom += 1;
                self.idxs.last_mut().unwrap().beta += 1;
                self.idxs.last_mut().unwrap().end += 1;
            }
            Redundant => {
                self.grid.insert(self.idxs.last().unwrap().redundant, fml);
                self.idxs.last_mut().unwrap().redundant += 1;
                self.idxs.last_mut().unwrap().quant += 1;
                self.idxs.last_mut().unwrap().atom += 1;
                self.idxs.last_mut().unwrap().beta += 1;
                self.idxs.last_mut().unwrap().end += 1;
            }
        }
    }

    pub(super) fn pop_fml(&mut self) -> Option<FormulaExtended<'a>> {
        use crate::new_prover::lang::Cost::*;
        let fml = self.grid.pop()?;
        match fml.cost {
            Alpha => {
                self.idxs.last_mut()?.end -= 1;
            }
            Beta(_) => {
                self.idxs.last_mut()?.beta -= 1;
                self.idxs.last_mut()?.end -= 1;
            }
            Atom => {
                self.idxs.last_mut()?.atom -= 1;
                self.idxs.last_mut()?.beta -= 1;
                self.idxs.last_mut()?.end -= 1;
            }
            Quant => {
                self.idxs.last_mut()?.quant -= 1;
                self.idxs.last_mut()?.atom -= 1;
                self.idxs.last_mut()?.beta -= 1;
                self.idxs.last_mut()?.end -= 1;
            }
            Redundant => {
                self.idxs.last_mut()?.redundant -= 1;
                self.idxs.last_mut()?.quant -= 1;
                self.idxs.last_mut()?.atom -= 1;
                self.idxs.last_mut()?.beta -= 1;
                self.idxs.last_mut()?.end -= 1;
            }
        }
        Some(fml)
    }

    /// Clones the last sequent and appends it to the grid and returns the new idx
    pub(super) fn clone_last_seq(&mut self) -> SequentIdx {
        // copy the last idx
        let mut idx = *self.idxs.last().unwrap();
        // copy each formula and push it to the grid
        for i in idx.start..idx.end {
            self.grid.push(self.grid[i]);
        }
        // update the new idx
        let len = idx.end - idx.start;
        idx.add_all(len);
        idx
    }

    pub(super) fn drop_last_seq(&mut self) {
        let idx = self.idxs.pop().unwrap();
        self.grid.truncate(idx.start);
    }
}
