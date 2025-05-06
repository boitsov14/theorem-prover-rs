use super::sequent::{Sequent, Side::*, SidedFormula};
use crate::{intern::Names, lang::Formula::*};
use log::trace;

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
    'outer: loop {
        trace!("Current remaining sequents:");
        for seq in &seqs {
            trace!("{}", seq.display(names).to_unicode());
        }
        // get the last sequent
        let Some(seq) = seqs.last_mut() else {
            trace!("All sequents are proved.");
            return true;
        };
        // pop the last formula
        let Some(SidedFormula { fml, side }) = seq.pop() else {
            // if `seq` has no formula, it is impossible to prove
            // this could happen:
            // ex. `true ⊢`, `true ∧ true ⊢`, `⊢ false`, `⊢ false ∨ false ∨ false`
            // all goes to `⊢` eventually
            return false;
        };
        match (fml, side) {
            // Convert `¬p ⊢` to `⊢ p`
            // Convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                let p = p.with_side(side.opposite());
                if seq.is_trivial(p) {
                    // if trivial, drop it and continue to the next sequent
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
                        // if trivial, drop it and continue to the next sequent
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
                    // when `fml` is redundant
                    // ex. `p ∨ q ∨ r, p ⊢`
                    // ex. `⊢ p ∧ q ∧ r, p`
                    // `fml` is already popped out, so nothing to do.
                    continue 'outer;
                }
                let mut l = l.iter().map(|p| p.with_side(side)).rev().peekable();
                let mut seq2;
                loop {
                    let Some(p) = l.next() else {
                        // when `⊢ true` or `false ⊢`
                        // or all of l is trivial
                        // the sequent is proved, so drop it and continue to the next sequent
                        seqs.pop().unwrap();
                        continue 'outer;
                    };
                    if seq.is_trivial(p) {
                        // if p is trivial, ignore it and continue to the next
                        continue;
                    }
                    if l.peek().is_none() {
                        seq.push(p);
                        // if p is last, continue to the next sequent
                        continue 'outer;
                    }
                    // if p is not last, need to clone the sequent
                    // because `seq` is the reference to the last element
                    seq2 = seq.clone();
                    seq.push(p);
                    break;
                }
                loop {
                    let Some(p) = l.next() else {
                        continue 'outer;
                    };
                    if seq2.is_trivial(p) {
                        continue;
                    }
                    // check p is last element of l
                    if l.peek().is_none() {
                        seq2.push(p);
                        seqs.push(seq2);
                        continue 'outer;
                    }
                    let mut seq2 = seq2.clone();
                    seq2.push(p);
                    seqs.push(seq2);
                }
            }
            // Convert `p → q ⊢` to `⊢ p` and `q ⊢`
            (To(p, q), Left) => {
                let q = q.with_side(Left);
                if q.is_atom() && seq.contains(&q) {
                    // when `fml` is redundant
                    // ex. `p → q, q ⊢`
                    // `fml` is already popped out, so nothing to do.
                    continue 'outer;
                }
                let p = p.with_side(Right);
                match (seq.is_trivial(p), seq.is_trivial(q)) {
                    (true, true) => {
                        // if trivial, drop it and continue to the next sequent
                        seqs.pop().unwrap();
                    }
                    (true, false) => {
                        // when q is yet to be proved
                        seq.push(q);
                    }
                    (false, true) => {
                        // when p is yet to be proved
                        seq.push(p);
                    }
                    (false, false) => {
                        // when both are yet to be proved
                        let mut seq2 = seq.clone();
                        seq.push(q);
                        seq2.push(p);
                        // `seq` is the reference to the last element, so don't need to push
                        seqs.push(seq2);
                    }
                }
            }
            // Convert `⊢ p → q` to `p ⊢ q`
            (To(p, q), Right) => {
                let p = p.with_side(Left);
                let q = q.with_side(Right);
                if seq.is_trivial2(p, q) {
                    // if trivial, drop it and continue to the next sequent
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
                match (seq.is_trivial2(fml11, fml12), seq.is_trivial2(fml21, fml22)) {
                    (true, true) => {
                        // if trivial, drop it
                        seqs.pop().unwrap();
                    }
                    (true, false) => {
                        // when the second is yet to be proved
                        seq.push(fml21);
                        seq.push(fml22);
                    }
                    (false, true) => {
                        // when the first is yet to be proved
                        seq.push(fml11);
                        seq.push(fml12);
                    }
                    (false, false) => {
                        // when both are yet to be proved
                        let mut seq2 = seq.clone();
                        seq.push(fml11);
                        seq.push(fml12);
                        seq2.push(fml21);
                        seq2.push(fml22);
                        seqs.push(seq2);
                    }
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
