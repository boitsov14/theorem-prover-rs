use super::sequent::{Sequent, Side::*, SidedFormula};
use crate::{intern::Names, lang::Formula::*};
use log::trace;
use std::vec;

pub fn prove_prop(seq: Sequent, names: &Names) -> bool {
    if seq.is_initially_trivial() {
        trace!("Trivial from the beginning: {}", seq.display(names).to_unicode());
        // ex. p, q ⊢ r, p
        return true;
    }
    let mut seqs = vec![seq];
    let mut temp_fmls = vec![];
    'outer: loop {
        trace!("Remainder:");
        for seq in seqs.iter().rev() {
            trace!("{}", seq.display(names).to_unicode());
        }
        // get the last sequent
        let Some(seq) = seqs.last_mut() else {
            trace!("All sequents are proved.");
            return true;
        };
        // pop the last formula
        let Some(SidedFormula { fml, side }) = seq.pop() else {
            trace!("Unprovable: No formula in the sequent.");
            // all the following examples go to `⊢` eventually
            // ex. `true ⊢`, `true ∧ true ⊢`, `⊢ false`, `⊢ false ∨ false ∨ false`
            return false;
        };
        match (fml, side) {
            // Convert `¬p ⊢` to `⊢ p`
            // Convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                let p = p.with_side(side.opposite());
                if seq.is_trivial(p) {
                    trace!("Trivial");
                    // drop it and continue to the next sequent
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(p);
            }
            // Convert `p ∧ q ∧ r ⊢` to `p, q, r ⊢`
            // Convert `⊢ p ∨ q ∨ r` to `⊢ p, q, r`
            // Convert `true ⊢` to `⊢`
            // Convert `⊢ false` to `⊢`
            (And(l), Left) | (Or(l), Right) => {
                for p in l {
                    let p = p.with_side(side);
                    if seq.is_trivial(p) {
                        trace!("Trivial");
                        // drop it and continue to the next sequent
                        seqs.pop().unwrap();
                        continue 'outer;
                    }
                    seq.push(p);
                }
            }
            // Convert `p ∨ q ∨ r ⊢` to `p ⊢` and `q ⊢` and `r ⊢`
            // Convert `⊢ p ∧ q ∧ r` to `⊢ p` and `⊢ q` and `⊢ r`
            // Drop `true ⊢` and `false ⊢`
            (And(l), Right) | (Or(l), Left) => {
                if l.iter()
                    .map(|p| p.with_side(side))
                    .any(|p| p.is_atom() && seq.contains(&p))
                {
                    trace!("The formula is redundant.");
                    // ex. `p ∨ q ∨ r, p ⊢`
                    // ex. `⊢ p ∧ q ∧ r, p`
                    // `fml` is already popped out, so nothing to do.
                    continue 'outer;
                }
                // exclude trivial fmls to reduce the clone cost of seq.
                for p in l {
                    let p = p.with_side(side);
                    if seq.is_trivial(p) {
                        trace!("Trivial");
                        continue;
                    }
                    temp_fmls.push(p);
                }
                if temp_fmls.is_empty() {
                    // ex. `⊢ true` or `false ⊢` (l is empty)
                    // ex. p, q, r ⊢ p ∧ q ∧ r (all of l is trivial)
                    // the sequent is proved, so drop it and continue to the next sequent
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                let mut current_seq = seq;
                while let Some(p) = temp_fmls.pop() {
                    if temp_fmls.is_empty() {
                        // if the last element
                        // push p to current seq without cloning
                        current_seq.push(p);
                    } else {
                        // If not the last element, clone current seq for the next fml
                        // push p to current seq
                        // then add the clone to seqs and make its reference to current seq
                        let next_seq = current_seq.clone();
                        current_seq.push(p);
                        seqs.push(next_seq);
                        current_seq = seqs.last_mut().unwrap();
                    }
                }
            }
            // Convert `p → q ⊢` to `⊢ p` and `q ⊢`
            (To(p, q), Left) => {
                let q = q.with_side(Left);
                if q.is_atom() && seq.contains(&q) {
                    trace!("The formula is redundant.");
                    // ex. `p → q, q ⊢`
                    // `fml` is already popped out, so nothing to do.
                    continue 'outer;
                }
                let p = p.with_side(Right);
                let p_is_trivial = seq.is_trivial(p);
                let q_is_trivial = seq.is_trivial(q);
                if p_is_trivial && q_is_trivial {
                    // both are trivial
                    trace!("Trivial");
                    trace!("Trivial");
                    // drop seq
                    seqs.pop().unwrap();
                } else if p_is_trivial {
                    trace!("Trivial");
                    // q is yet to be proved
                    seq.push(q);
                } else if q_is_trivial {
                    trace!("Trivial");
                    // p is yet to be proved
                    seq.push(p);
                } else {
                    // both are yet to be proved
                    let mut seq2 = seq.clone();
                    seq.push(q);
                    seq2.push(p);
                    // `seq` is the reference to the last element, so don't need to push
                    seqs.push(seq2);
                }
            }
            // Convert `⊢ p → q` to `p ⊢ q`
            (To(p, q), Right) => {
                let p = p.with_side(Left);
                let q = q.with_side(Right);
                if seq.is_trivial2(p, q) {
                    trace!("Trivial");
                    // drop it and continue to the next sequent
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(p);
                seq.push(q);
            }
            // Convert `p ↔ q ⊢` to `p, q ⊢` and `⊢ p, q`
            // Convert `⊢ p ↔ q` to `p ⊢ q` and `q ⊢ p`
            (Iff(p, q), side) => {
                let p_l = p.with_side(Left);
                let p_r = p.with_side(Right);
                let q_l = q.with_side(Left);
                let q_r = q.with_side(Right);
                let (fml11, fml12, fml21, fml22) = match side {
                    Left => (p_r, q_r, p_l, q_l),
                    Right => (q_l, p_r, p_l, q_r),
                };
                let fml1_is_trivial = seq.is_trivial2(fml11, fml12);
                let fml2_is_trivial = seq.is_trivial2(fml21, fml22);
                if fml1_is_trivial && fml2_is_trivial {
                    // both are trivial
                    trace!("Trivial");
                    trace!("Trivial");
                    // drop seq
                    seqs.pop().unwrap();
                } else if fml1_is_trivial {
                    trace!("Trivial");
                    // the second is yet to be proved
                    seq.push(fml21);
                    seq.push(fml22);
                } else if fml2_is_trivial {
                    trace!("Trivial");
                    // the first is yet to be proved
                    seq.push(fml11);
                    seq.push(fml12);
                } else {
                    // both are yet to be proved
                    let mut seq2 = seq.clone();
                    seq.push(fml11);
                    seq.push(fml12);
                    seq2.push(fml21);
                    seq2.push(fml22);
                    seqs.push(seq2);
                }
            }
            // since formulas in 'seq' are ordered,
            // if `fml` is predicate, no formulas can be processed
            // thus, it is impossible to prove
            (Pred(..), _) => return false,
            (Ex(..) | All(..), _) => unimplemented!(),
        }
    }
}
