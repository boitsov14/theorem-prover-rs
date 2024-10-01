use crate::lang::{Formula::*, Sequent};
use crate::name::Names;
use crate::new_prover2::lang::Side::{Left, Right};
use crate::new_prover2::lang::{FormulaExtended, SequentExtended, SequentWithArity};

pub fn prove_prop(seq: &Sequent, names: &Names) -> bool {
    let ant = &seq.ant;
    let suc = &seq.suc;
    let mut seq = SequentExtended::default();
    for fml in ant {
        let fml = fml.extended(Left);
        if seq.is_trivial(fml) {
            return true;
        }
        seq.push(fml);
    }
    for fml in suc {
        let fml = fml.extended(Right);
        if seq.is_trivial(fml) {
            return true;
        }
        seq.push(fml);
    }
    let mut seqs = vec![seq];
    'outer: loop {
        if cfg!(debug_assertions) {
            for seq in &seqs {
                println!("{}", seq.to_seq().display(names));
            }
            println!();
        }
        let Some(seq) = seqs.last_mut() else {
            return true;
        };
        let Some(fml_ext) = seq.pop() else {
            return false;
        };
        let FormulaExtended { fml, side } = fml_ext;
        match (fml, side) {
            (Not(p), _) => {
                let p = p.extended(side.opposite());
                if seq.is_trivial(p) {
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(p);
            }
            (And(l), Left) | (Or(l), Right) => {
                for p in l {
                    let p = p.extended(side);
                    if seq.is_trivial(p) {
                        seqs.pop().unwrap();
                        continue 'outer;
                    }
                    seq.push(p);
                }
            }
            (And(l), Right) | (Or(l), Left) => {
                if l.iter()
                    .map(|p| p.extended(side))
                    .any(|p| p.is_atom() && seq.contains(&p))
                {
                    // when fml is redundant
                    // fml is already popped out, so nothing to do.
                    continue 'outer;
                }
                let mut l = l.iter().rev().peekable();
                let mut seq2;
                loop {
                    let Some(p) = l.next() else {
                        // when `|- true` or `false |-` or all of l is trivial
                        seqs.pop().unwrap();
                        continue 'outer;
                    };
                    let p = p.extended(side);
                    if seq.is_trivial(p) {
                        continue;
                    }
                    seq2 = seq.clone();
                    seq.push(p);
                    break;
                }
                loop {
                    let Some(p) = l.next() else {
                        continue 'outer;
                    };
                    let p = p.extended(side);
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
            (To(p, q), Left) => {
                let p = p.extended(Right);
                let q = q.extended(Left);
                if q.is_atom() && seq.contains(&q) {
                    // when fml is redundant
                    // fml is already popped out, so nothing to do.
                    continue 'outer;
                }
                if seq.is_trivial(q) {
                    if seq.is_trivial(p) {
                        // when both p and q are trivial
                        seqs.pop().unwrap();
                    } else {
                        // when only q is trivial
                        seq.push(p);
                    }
                } else if seq.is_trivial(p) {
                    // when only p is trivial
                    seq.push(q);
                } else {
                    // when both p and q are not trivial
                    let mut seq2 = seq.clone();
                    seq.push(q);
                    seq2.push(p);
                    seqs.push(seq2);
                }
            }
            (To(p, q), Right) => {
                let p = p.extended(Left);
                let q = q.extended(Right);
                if seq.is_trivial(p) {
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(p);
                if seq.is_trivial(q) {
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(q);
            }
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
