use crate::lang::Formula::*;
use crate::lang::{Sequent, FALSE, TRUE};
use crate::name::Names;
use crate::new_prover2::lang::Side::{Left, Right};
use crate::new_prover2::lang::{FormulaExtended, SequentExtended};

impl<'a> SequentExtended<'a> {
    #[inline(always)]
    fn is_trivial(&self, fml: FormulaExtended<'a>) -> bool {
        (fml.is_atom() && self.contains(&fml.opposite())) || {
            let FormulaExtended { fml, side } = fml;
            (fml == &TRUE && side == Right) || (fml == &FALSE && side == Left)
        }
    }
}

pub fn prove_prop(seq: &Sequent, names: &Names) -> bool {
    let seq = seq.extended();
    let seqs = &mut vec![seq];
    // TODO: 2024/08/25 popではなくlast_mutの使用を検討
    'outer: while let Some(mut seq) = seqs.pop() {
        if cfg!(debug_assertions) {
            for seq in seqs.iter() {
                println!("{}", seq.to_seq().display(names));
            }
            println!("{}", seq.to_seq().display(names));
            println!();
        }
        let Some(FormulaExtended { fml, side }) = seq.pop() else {
            return false;
        };
        match (fml, side) {
            (Not(p), _) => {
                let p = p.extended(side.opposite());
                if !seq.is_trivial(p) {
                    seq.push(p);
                    seqs.push(seq);
                }
            }
            (And(l), Left) | (Or(l), Right) => {
                for p in l {
                    let p = p.extended(side);
                    if seq.is_trivial(p) {
                        continue 'outer;
                    }
                    seq.push(p);
                }
                seqs.push(seq);
            }
            (And(l), Right) | (Or(l), Left) => {
                if l.iter()
                    .any(|p| p.is_atom() && seq.contains(&p.extended(side)))
                {
                    seqs.push(seq);
                    continue 'outer;
                }
                let (p, l) = l.split_first().unwrap();
                for p in l.iter().rev() {
                    let p = p.extended(side);
                    if !seq.is_trivial(p) {
                        let mut seq = seq.clone();
                        seq.push(p);
                        seqs.push(seq);
                    }
                }
                let p = p.extended(side);
                if !seq.is_trivial(p) {
                    seq.push(p);
                    seqs.push(seq);
                }
            }
            (To(p, q), Left) => {
                let p = p.extended(Right);
                let q = q.extended(Left);
                if q.is_atom() && seq.contains(&q) {
                    seqs.push(seq);
                    continue 'outer;
                }
                if !seq.is_trivial(q) {
                    let mut seq = seq.clone();
                    seq.push(q);
                    seqs.push(seq);
                }
                if !seq.is_trivial(p) {
                    seq.push(p);
                    seqs.push(seq);
                }
            }
            (To(p, q), Right) => {
                let p = p.extended(Left);
                let q = q.extended(Right);
                if seq.is_trivial(p) {
                    continue 'outer;
                }
                seq.push(p);
                if seq.is_trivial(q) {
                    continue 'outer;
                }
                seq.push(q);
                seqs.push(seq);
            }
            (Iff(p, q), Left) => {
                let p_r = p.extended(Right);
                let q_r = q.extended(Right);
                if !seq.is_trivial(p_r) && !seq.is_trivial(q_r) {
                    let mut seq = seq.clone();
                    seq.push(p_r);
                    seq.push(q_r);
                    seqs.push(seq);
                }
                let p_l = p.extended(Left);
                let q_l = q.extended(Left);
                if !seq.is_trivial(p_l) && !seq.is_trivial(q_l) {
                    seq.push(p_l);
                    seq.push(q_l);
                    seqs.push(seq);
                }
            }
            (Iff(p, q), Right) => {
                let p_r = p.extended(Right);
                let q_l = q.extended(Left);
                if !(seq.is_trivial(p_r) || seq.is_trivial(q_l)) {
                    let mut seq = seq.clone();
                    seq.push(p_r);
                    seq.push(q_l);
                    seqs.push(seq);
                }
                let p_l = p.extended(Left);
                let q_r = q.extended(Right);
                if !(seq.is_trivial(p_l) || seq.is_trivial(q_r)) {
                    seq.push(p_l);
                    seq.push(q_r);
                    seqs.push(seq);
                }
            }
            (Pred(_, _), _) => return false,
            (Ex(_, _) | All(_, _), _) => unimplemented!(),
        }
    }
    true
}
