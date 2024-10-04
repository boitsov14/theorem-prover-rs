use crate::lang::{Formula::*, Sequent};
use crate::name::Names;
use crate::new_prover2::lang::Side::{Left, Right};
use crate::new_prover2::lang::{FormulaExtended, SequentExtended};

// impl Sequent
impl Sequent<'_> {
    fn extended(&self) -> Option<SequentExtended> {
        let mut seq = SequentExtended::default();
        for fml in &self.ant {
            let fml = fml.extended(Left);
            if seq.is_trivial(fml) {
                return None;
            }
            seq.push(fml);
        }
        for fml in &self.suc {
            let fml = fml.extended(Right);
            if seq.is_trivial(fml) {
                return None;
            }
            seq.push(fml);
        }
        Some(seq)
    }
}

fn log_seqs(seqs: &[SequentExtended], names: &Names) {
    for seq in seqs {
        println!("{}", seq.to_seq().display(names));
    }
}

pub fn prove_prop(seq: &Sequent, names: &Names) -> bool {
    let Some(seq) = seq.extended() else {
        return true;
    };
    let mut seqs = vec![seq];
    'outer: loop {
        #[cfg(debug_assertions)]
        log_seqs(&seqs, names);
        // get the last sequent
        let Some(seq) = seqs.last_mut() else {
            // if no sequent to be proved, completed the proof
            return true;
        };
        // pop the last formula
        let Some(FormulaExtended { fml, side }) = seq.pop() else {
            // if no formula to be processed, failed to prove
            return false;
        };
        match (fml, side) {
            // Convert `¬p ⊢` to `⊢ p`
            // Convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                let p = p.extended(side.opposite());
                if seq.is_trivial(p) {
                    // if the sequent is proved, drop it and continue to the next sequent
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(p);
            }
            // Convert `p ∧ q ∧ r ⊢` to `p, q, r ⊢`
            // Convert `⊢ p ∨ q ∨ r` to `⊢ p, q, r`
            (And(l), Left) | (Or(l), Right) => {
                for p in l {
                    let p = p.extended(side);
                    if seq.is_trivial(p) {
                        // if the sequent is proved, drop it and continue to the next sequent
                        seqs.pop().unwrap();
                        continue 'outer;
                    }
                    seq.push(p);
                }
            }
            // Convert `p ∨ q ∨ r ⊢` to `p ⊢` and `q ⊢` and `r ⊢`
            // Convert `⊢ p ∧ q ∧ r` to `⊢ p` and `⊢ q` and `⊢ r`
            (And(l), Right) | (Or(l), Left) => {
                if l.iter()
                    .map(|p| p.extended(side))
                    .any(|p| p.is_atom() && seq.contains(&p))
                {
                    // when `fml` is redundant
                    // `fml` is already popped out, so nothing to do.
                    continue 'outer;
                }
                let mut l = l.iter().map(|p| p.extended(side)).rev().peekable();
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
                let q = q.extended(Left);
                if q.is_atom() && seq.contains(&q) {
                    // when `fml` is redundant
                    // `fml` is already popped out, so nothing to do.
                    continue 'outer;
                }
                let p = p.extended(Right);
                match (seq.is_trivial(p), seq.is_trivial(q)) {
                    (true, true) => {
                        // if the sequent is proved, drop it and continue to the next sequent
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
                        seq.push(p);
                        seq2.push(q);
                        // `seq` is the reference to the last element, so don't need to push
                        seqs.push(seq2);
                    }
                }
            }
            // Convert `⊢ p → q` to `p ⊢ q`
            (To(p, q), Right) => {
                let p = p.extended(Left);
                if seq.is_trivial(p) {
                    // if the sequent is proved, drop it and continue to the next sequent
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(p);
                let q = q.extended(Right);
                if seq.is_trivial(q) {
                    // if the sequent is proved, drop it and continue to the next sequent
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(q);
            }
            // Convert `p ↔ q ⊢` to `p, q ⊢` and `⊢ p, q`
            // Convert `⊢ p ↔ q` to `p ⊢ q` and `q ⊢ p`
            // (Iff(p, q), side) => {}
            (Iff(p, q), Left) => {
                let p_r = p.extended(Right);
                let q_r = q.extended(Right);
                let p_l = p.extended(Left);
                let q_l = q.extended(Left);
                if seq.is_trivial(p_r) || seq.is_trivial(q_r) {
                    if seq.is_trivial(p_l) || seq.is_trivial(q_l) {
                        // when both are trivial
                        seqs.pop().unwrap();
                    } else {
                        // when only the first is trivial
                        seq.push(p_l);
                        seq.push(q_l);
                    }
                } else if seq.is_trivial(p_l) || seq.is_trivial(q_l) {
                    // when only the second is trivial
                    seq.push(p_r);
                    seq.push(q_r);
                } else {
                    // when both are not trivial
                    let mut seq2 = seq.clone();
                    seq.push(p_r);
                    seq.push(q_r);
                    seq2.push(p_l);
                    seq2.push(q_l);
                    seqs.push(seq2);
                }
            }
            (Iff(p, q), Right) => {
                let p_r = p.extended(Right);
                let q_r = q.extended(Right);
                let p_l = p.extended(Left);
                let q_l = q.extended(Left);
                if seq.is_trivial(p_r) || seq.is_trivial(q_l) {
                    if seq.is_trivial(p_l) || seq.is_trivial(q_r) {
                        // when both are trivial
                        seqs.pop().unwrap();
                    } else {
                        // when only the first is trivial
                        seq.push(p_l);
                        seq.push(q_r);
                    }
                } else if seq.is_trivial(p_l) || seq.is_trivial(q_r) {
                    // when only the second is trivial
                    seq.push(p_r);
                    seq.push(q_l);
                } else {
                    // when both are not trivial
                    let mut seq2 = seq.clone();
                    seq.push(p_l);
                    seq.push(q_r);
                    seq2.push(p_r);
                    seq2.push(q_l);
                    seqs.push(seq2);
                }
            }
            (Pred(_, _), _) => return false,
            (Ex(_, _) | All(_, _), _) => unimplemented!(),
        }
    }
}
