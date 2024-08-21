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

    pub(super) fn prove_prop(&mut self) -> bool {
        while let Some(fml) = self.pop_fml() {
            match (fml.fml, fml.side) {
                (Not(p), _) => {
                    // add the inner formula to the opposite side
                    let new_p = FormulaExtended::new(p, fml.side.opposite());
                    if self.is_trivial(new_p) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_p);
                }
                (And(l), Left) | (Or(l), Right) => {
                    // add all formulas to the same side
                    for p in l {
                        let new_p = FormulaExtended::new(p, fml.side);
                        if self.is_trivial(new_p) {
                            self.drop_last_seq();
                            continue;
                        }
                        self.push_fml(new_p);
                    }
                }
                (And(l), Right) | (Or(l), Left) => {
                    // TODO: 2024/08/20 costがなければもっとシンプルに書ける
                    // check if the formula is redundant
                    if l.iter().any(|p| {
                        self.last_seq()
                            .unwrap()
                            .iter()
                            .any(|q| q.fml == p && q.side == fml.side)
                    }) {
                        let mut fml = fml;
                        fml.cost = Cost::Redundant;
                        self.push_fml(fml);
                        continue;
                    }
                    let (p0, l) = l.split_first().unwrap();
                    // add p0 to the same side
                    let new_p = FormulaExtended::new(p0, fml.side);
                    if self.is_trivial(new_p) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_p);
                    // add all others to the same side with a new sequent
                    for p in l {
                        // add a new sequent
                        self.clone_last_seq();
                        // add p to the same side
                        let new_p = FormulaExtended::new(p, fml.side);
                        if self.is_trivial(new_p) {
                            self.drop_last_seq();
                            continue;
                        }
                        self.push_fml(new_p);
                    }
                }
                (To(p, q), Left) => {
                    // add p to the right side
                    let new_p = FormulaExtended::new(p, Right);
                    if self.is_trivial(new_p) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_p);
                    // add a new sequent
                    self.clone_last_seq();
                    // add q to the left side
                    let new_q = FormulaExtended::new(q, Left);
                    if self.is_trivial(new_q) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_q);
                }
                (To(p, q), Right) => {
                    // add p to the left side and q to the right side
                    let new_p = FormulaExtended::new(p, Left);
                    if self.is_trivial(new_p) {
                        self.drop_last_seq();
                        continue;
                    }
                    let new_q = FormulaExtended::new(q, Right);
                    if self.is_trivial(new_q) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_p);
                    self.push_fml(new_q);
                }
                (Iff(p, q), Left) => {
                    // check if the formula is redundant
                    // TODO: 2024/08/21
                    // add p and q to the left side
                    let new_p = FormulaExtended::new(p, Left);
                    if self.is_trivial(new_p) {
                        self.drop_last_seq();
                        continue;
                    }
                    let new_q = FormulaExtended::new(q, Left);
                    if self.is_trivial(new_q) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_p);
                    self.push_fml(new_q);
                    // add a new sequent
                    self.clone_last_seq();
                    // add p and q to the right side
                    let new_p = FormulaExtended::new(p, Right);
                    if self.is_trivial(new_p) {
                        self.drop_last_seq();
                        continue;
                    }
                    let new_q = FormulaExtended::new(q, Right);
                    if self.is_trivial(new_q) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_p);
                    self.push_fml(new_q);
                }
                (Iff(p, q), Right) => {
                    // check if the formula is redundant
                    // TODO: 2024/08/21
                    // add p to the left side and q to the right side
                    let new_p = FormulaExtended::new(p, Left);
                    if self.is_trivial(new_p) {
                        self.drop_last_seq();
                        continue;
                    }
                    let new_q = FormulaExtended::new(q, Right);
                    if self.is_trivial(new_q) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_p);
                    self.push_fml(new_q);
                    // add a new sequent
                    self.clone_last_seq();
                    // add p to the right side and q to the left side
                    let new_p = FormulaExtended::new(p, Right);
                    if self.is_trivial(new_p) {
                        self.drop_last_seq();
                        continue;
                    }
                    let new_q = FormulaExtended::new(q, Left);
                    if self.is_trivial(new_q) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(new_p);
                    self.push_fml(new_q);
                }
                (Pred(_, _), _) => return false,
                (Ex(_, _) | All(_, _), _) => unimplemented!(),
            }
        }
        true
    }
}
