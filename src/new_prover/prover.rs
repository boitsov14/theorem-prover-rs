use crate::lang::{Formula::*, FALSE, TRUE};
use crate::new_prover::lang::{
    Cost, FormulaExtended,
    Side::{Left, Right},
};
use crate::new_prover::sequent_grid::SequentGrid;

impl<'a> SequentGrid<'a> {
    fn is_trivial(&self, fml: FormulaExtended<'a>) -> bool {
        (*fml.fml == TRUE && fml.side == Right)
            || (*fml.fml == FALSE && fml.side == Left)
            || (fml.fml.is_atom()
                && self
                    .last_atom()
                    .unwrap()
                    .iter()
                    .any(|p| p.fml == fml.fml && p.side != fml.side))
    }

    fn prove_prop(&mut self) -> bool {
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
                    let mut idx = *self.idxs.last().unwrap();
                    idx.start = self.len();
                    for i in idx.start..self.len() - 1 {
                        self.grid.push(self.grid[i]);
                    }
                    self.idxs.push(idx);
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
