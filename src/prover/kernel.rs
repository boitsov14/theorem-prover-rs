use crate::{
    intern::Names,
    lang::Formula::*,
    prover::sequent::{Sequent, Side::*, SidedFormula},
};
use log::trace;
use std::vec;

pub fn prove_prop(seq: Sequent, names: &Names) -> bool {
    if seq.is_initially_trivial() {
        trace!(
            "Trivial from the beginning: {}",
            seq.display(names).to_unicode()
        );
        // ex. p, q ⊢ r, p
        return true;
    }
    let mut seqs = vec![seq];
    let mut temp_fmls = vec![];
    'main: loop {
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
                    continue 'main;
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
                        continue 'main;
                    }
                    seq.push(p);
                }
            }
            // Convert `p ∨ q ∨ r ⊢` to `p ⊢` and `q ⊢` and `r ⊢`
            // Convert `⊢ p ∧ q ∧ r` to `⊢ p` and `⊢ q` and `⊢ r`
            // Drop `⊢ true` and `false ⊢`
            (And(l), Right) | (Or(l), Left) => {
                if l.iter()
                    .map(|p| p.with_side(side))
                    .any(|p| p.is_atom() && seq.contains_atom(&p))
                {
                    trace!("The formula is redundant.");
                    // ex. `p ∨ q ∨ r, p ⊢`
                    // ex. `⊢ p ∧ q ∧ r, p`
                    // `fml` is already popped out, so nothing to do.
                    continue 'main;
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
                    continue 'main;
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
                if q.is_atom() && seq.contains_atom(&q) {
                    trace!("The formula is redundant.");
                    // ex. `p → q, q ⊢`
                    // `fml` is already popped out, so nothing to do.
                    continue 'main;
                }
                let p = p.with_side(Right);
                let is_trivial_p = seq.is_trivial(p);
                let is_trivial_q = seq.is_trivial(q);
                if is_trivial_p && is_trivial_q {
                    // both are trivial
                    trace!("Trivial");
                    trace!("Trivial");
                    // drop seq
                    seqs.pop().unwrap();
                } else if is_trivial_p {
                    trace!("Trivial");
                    // q is yet to be proved
                    seq.push(q);
                } else if is_trivial_q {
                    trace!("Trivial");
                    // p is yet to be proved
                    seq.push(p);
                } else {
                    // both are yet to be proved
                    // we need to process `seq1` first, so `seq1` must come AFTER `seq2` in `seqs` stack
                    // `seq2` is the reference to the last element, so don't need to push `seq2`
                    let mut seq1 = seq.clone();
                    let seq2 = seq;
                    seq1.push(p);
                    seq2.push(q);
                    seqs.push(seq1);
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
                    continue 'main;
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
                    Left => (p_l, q_l, p_r, q_r),
                    Right => (p_l, q_r, q_l, p_r),
                };
                let is_trivial1 = seq.is_trivial2(fml11, fml12);
                let is_trivial2 = seq.is_trivial2(fml21, fml22);
                if is_trivial1 && is_trivial2 {
                    // both are trivial
                    trace!("Trivial");
                    trace!("Trivial");
                    // drop seq
                    seqs.pop().unwrap();
                } else if is_trivial1 {
                    trace!("Trivial");
                    // the second is yet to be proved
                    seq.push(fml21);
                    seq.push(fml22);
                } else if is_trivial2 {
                    trace!("Trivial");
                    // the first is yet to be proved
                    seq.push(fml11);
                    seq.push(fml12);
                } else {
                    // both are yet to be proved
                    // we need to process `seq1` first, so `seq1` must come AFTER `seq2` in `seqs` stack
                    // `seq2` is the reference to the last element, so don't need to push `seq2`
                    let mut seq1 = seq.clone();
                    let seq2 = seq;
                    seq1.push(fml11);
                    seq1.push(fml12);
                    seq2.push(fml21);
                    seq2.push(fml22);
                    seqs.push(seq1);
                }
            }
            (Pred(..), _) => unreachable!(),
            (Ex(..) | All(..), _) => unimplemented!(),
        }
    }
}
