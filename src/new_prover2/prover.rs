use crate::lang::Formula::*;
use crate::lang::{FALSE, TRUE};
use crate::new_prover2::lang::Side::{Left, Right};
use crate::new_prover2::lang::{FormulaExtended, SequentExtended};

impl<'a> SequentExtended<'a> {
    #[inline]
    fn is_trivial(&self, fml: FormulaExtended<'a>) -> bool {
        fml == FormulaExtended::init(&TRUE, Right)
            || fml == FormulaExtended::init(&FALSE, Left)
            || self.contains(&fml.opposite())
    }

    #[inline]
    fn is_redundant(&self, fml: &FormulaExtended<'a>) -> bool {
        self.contains(fml)
    }
}

pub(super) fn prove_prop(seqs: &mut Vec<SequentExtended>) -> bool {
    let mut redundant_i: usize = 0;
    let mut iter: usize = 0;
    // TODO: 2024/08/25 popではなくlast_mutの使用を検討
    while let Some(mut seq) = seqs.pop() {
        iter += 1;
        let FormulaExtended { fml, side } = seq.pop().unwrap();
        match (fml, side) {
            (Not(p), _) => {
                // add the inner formula to the opposite side
                let p = FormulaExtended::init(p, side.opposite());
                if seq.is_trivial(p) {
                    // TODO: 2024/08/25
                } else {
                    seq.push(p);
                    seqs.push(seq);
                }
            }
            (And(l), Left) | (Or(l), Right) => {
                // add all formulas to the same side
                for p in l {
                    let p = FormulaExtended::init(p, side);
                    if seq.is_trivial(p) {
                        break;
                    }
                    seq.push(p);
                }
                seqs.push(seq);
            }
            (And(l), Right) | (Or(l), Left) => {
                // check if the formula is redundant
                if l.iter()
                    .any(|p| seq.is_redundant(&FormulaExtended::init(p, side)))
                {
                    redundant_i += 1;
                    continue;
                }
                for (i, p) in l.iter().enumerate() {
                    let p = FormulaExtended::init(p, side);
                    if i == l.len() - 1 {
                        if seq.is_trivial(p) {
                            // TODO: 2024/08/25
                        } else {
                            seq.push(p);
                            seqs.push(seq);
                        }
                        break;
                    }
                    if seq.is_trivial(p) {
                        // TODO: 2024/08/25
                    } else {
                        let mut seq = seq.clone();
                        seq.push(p);
                        seqs.push(seq);
                    }
                }
            }
            (To(p, q), Left) => {
                // check if the formula is redundant
                let p = FormulaExtended::init(p, Right);
                if !seq.is_trivial(p) {
                    let mut seq = seq.clone();
                    seq.push(p);
                    seqs.push(seq);
                }
                let q = FormulaExtended::init(q, Left);
                if seq.is_trivial(q) {
                } else {
                    seq.push(q);
                    seqs.push(seq);
                }
            }
            (To(p, q), Right) => {
                // add p to the left side and q to the right side
                let p = FormulaExtended::init(p, Left);
                let q = FormulaExtended::init(q, Right);
                if seq.is_trivial(p) || seq.is_trivial(q) {
                    continue;
                }
                seq.push(p);
                seq.push(q);
                seqs.push(seq);
            }
            (Iff(p, q), Left) => {
                // check if the formula is redundant
                // TODO: 2024/08/21
                let p_l = FormulaExtended::init(p, Left);
                let q_l = FormulaExtended::init(q, Left);
                if !(seq.is_trivial(p_l) || seq.is_trivial(q_l)) {
                    let mut seq = seq.clone();
                    seq.push(p_l);
                    seq.push(q_l);
                    seqs.push(seq);
                }
                let p_r = FormulaExtended::init(p, Right);
                let q_r = FormulaExtended::init(q, Right);
                if !(seq.is_trivial(p_r) || seq.is_trivial(q_r)) {
                    let mut seq = seq.clone();
                    seq.push(p_r);
                    seq.push(q_r);
                    seqs.push(seq);
                }
            }
            (Iff(p, q), Right) => {
                // check if the formula is redundant
                // TODO: 2024/08/21
                let p_l = FormulaExtended::init(p, Left);
                let q_r = FormulaExtended::init(q, Right);
                if !(seq.is_trivial(p_l) || seq.is_trivial(q_r)) {
                    let mut seq = seq.clone();
                    seq.push(p_l);
                    seq.push(q_r);
                    seqs.push(seq);
                }
                let p_r = FormulaExtended::init(p, Right);
                let q_l = FormulaExtended::init(q, Left);
                if !(seq.is_trivial(p_r) || seq.is_trivial(q_l)) {
                    let mut seq = seq.clone();
                    seq.push(p_r);
                    seq.push(q_l);
                    seqs.push(seq);
                }
            }
            (Pred(_, _), _) => return false,
            (Ex(_, _) | All(_, _), _) => unimplemented!(),
        }
    }
    println!("iter: {iter}");
    println!("redundant: {redundant_i}");
    true
}
