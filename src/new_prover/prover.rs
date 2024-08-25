use crate::lang::{Formula::*, FALSE, TRUE};
use crate::new_prover::lang::{
    Cost, FormulaExtended,
    Side::{Left, Right},
};
use crate::new_prover::sequent_grid::SequentGrid;
use itertools::Itertools;

impl<'a> SequentGrid<'a> {
    #[inline]
    // TODO: 2024/08/24 containsを使ってパフォーマンス比較
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

    #[inline]
    fn is_redundant(&self, fml: &FormulaExtended<'a>) -> bool {
        self.last_atom().unwrap().iter().contains(fml)
    }

    pub(super) fn prove_prop(&mut self) -> bool {
        let mut redundant_i: usize = 0;
        let mut iter: usize = 0;
        while let Some(fml) = self.pop_fml() {
            iter += 1;
            match (fml.fml, fml.side) {
                (Not(p), _) => {
                    // add the inner formula to the opposite side
                    let p = FormulaExtended::new(p, fml.side.opposite());
                    if self.is_trivial(p) {
                        self.drop_last_seq();
                    } else {
                        self.push_fml(p);
                    }
                }
                (And(l), Left) | (Or(l), Right) => {
                    // add all formulas to the same side
                    for p in l {
                        let p = FormulaExtended::new(p, fml.side);
                        if self.is_trivial(p) {
                            self.drop_last_seq();
                            break;
                        }
                        self.push_fml(p);
                    }
                }
                (And(l), Right) | (Or(l), Left) => {
                    // TODO: 2024/08/20 costがなければもっとシンプルに書ける
                    // check if the formula is redundant
                    if l.iter().any(|p| {
                        p.is_atom() && self.is_redundant(&FormulaExtended::new(p, fml.side))
                    }) {
                        redundant_i += 1;
                        let mut fml = fml;
                        fml.cost = Cost::Redundant;
                        self.push_fml(fml);
                        continue;
                    }
                    for (i, p) in l.iter().enumerate() {
                        let p = FormulaExtended::new(p, fml.side);
                        if i == l.len() - 1 {
                            if self.is_trivial(p) {
                                self.drop_last_seq();
                                break;
                            }
                            // if p is last, just push it
                            self.push_fml(p);
                        } else {
                            if self.is_trivial(p) {
                                // don't drop the last sequent to use it for the next iteration
                                continue;
                            }
                            // if p is not last, clone the sequent for the next iteration, then push p
                            let mut idx = self.clone_last_seq();
                            idx.add_all(1);
                            self.push_fml(p);
                            self.idxs.push(idx);
                        }
                    }
                }
                (To(p, q), Left) => {
                    // check if the formula is redundant
                    // TODO: 2024/08/21
                    let p = FormulaExtended::new(p, Right);
                    if !self.is_trivial(p) {
                        // clone the sequent for q, then push p
                        let mut idx = self.clone_last_seq();
                        idx.add_all(1);
                        self.push_fml(p);
                        self.idxs.push(idx);
                    }
                    let q = FormulaExtended::new(q, Left);
                    if self.is_trivial(q) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(q);
                }
                (To(p, q), Right) => {
                    // add p to the left side and q to the right side
                    let p = FormulaExtended::new(p, Left);
                    let q = FormulaExtended::new(q, Right);
                    if self.is_trivial(p) || self.is_trivial(q) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(p);
                    self.push_fml(q);
                }
                (Iff(p, q), Left) => {
                    // check if the formula is redundant
                    // TODO: 2024/08/21
                    let p_l = FormulaExtended::new(p, Left);
                    let q_l = FormulaExtended::new(q, Left);
                    if !(self.is_trivial(p_l) || self.is_trivial(q_l)) {
                        // clone the sequent for p_r and q_r, then push p_l and q_l
                        let mut idx = self.clone_last_seq();
                        idx.add_all(2);
                        self.push_fml(p_l);
                        self.push_fml(q_l);
                        self.idxs.push(idx);
                    }
                    let p_r = FormulaExtended::new(p, Right);
                    let q_r = FormulaExtended::new(q, Right);
                    if self.is_trivial(p_r) || self.is_trivial(q_r) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(p_r);
                    self.push_fml(q_r);
                }
                (Iff(p, q), Right) => {
                    // check if the formula is redundant
                    // TODO: 2024/08/21
                    let p_l = FormulaExtended::new(p, Left);
                    let q_r = FormulaExtended::new(q, Right);
                    if !(self.is_trivial(p_l) || self.is_trivial(q_r)) {
                        // clone the sequent for p_r and q_l, then push p_r and q_l
                        let mut idx = self.clone_last_seq();
                        idx.add_all(2);
                        self.push_fml(p_l);
                        self.push_fml(q_r);
                        self.idxs.push(idx);
                    }
                    let p_r = FormulaExtended::new(p, Right);
                    let q_l = FormulaExtended::new(q, Left);
                    if self.is_trivial(p_r) || self.is_trivial(q_l) {
                        self.drop_last_seq();
                        continue;
                    }
                    self.push_fml(p_r);
                    self.push_fml(q_l);
                }
                (Pred(_, _), _) => return false,
                (Ex(_, _) | All(_, _), _) => unimplemented!(),
            }
        }
        println!("iter: {iter}");
        println!("redundant: {redundant_i}");
        true
    }
}
