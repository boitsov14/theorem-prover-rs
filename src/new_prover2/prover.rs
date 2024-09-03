use crate::lang::Formula::*;
use crate::lang::{FALSE, TRUE};
use crate::name::Names;
use crate::new_prover2::lang::Side::{Left, Right};
use crate::new_prover2::lang::{FormulaExtended, SequentExtended};

impl<'a> SequentExtended<'a> {
    #[inline(always)]
    fn is_trivial(&self, fml: FormulaExtended<'a>) -> bool {
        fml == FormulaExtended::init(&TRUE, Right)
            || fml == FormulaExtended::init(&FALSE, Left)
            || (fml.is_atom() && self.contains(&fml.opposite()))
    }
}

pub(super) fn prove_prop(seqs: &mut Vec<SequentExtended>, names: &Names) -> bool {
    let mut redundant_i: usize = 0;
    let mut iter: usize = 0;
    // TODO: 2024/08/25 popではなくlast_mutの使用を検討
    'outer: while let Some(mut seq) = seqs.pop() {
        if cfg!(debug_assertions) {
            for seq in seqs.iter() {
                println!("{}", seq.to_sequent().display(names));
            }
            println!("{}", seq.to_sequent().display(names));
            println!("----------------");
        }
        iter += 1;
        let FormulaExtended { fml, side } = seq.pop().unwrap();
        match (fml, side) {
            (Not(p), _) => {
                let p = FormulaExtended::init(p, side.opposite());
                if !seq.is_trivial(p) {
                    seq.push(p);
                    seqs.push(seq);
                }
            }
            (And(l), Left) | (Or(l), Right) => {
                for p in l {
                    let p = FormulaExtended::init(p, side);
                    if seq.is_trivial(p) {
                        continue 'outer;
                    }
                    seq.push(p);
                }
                seqs.push(seq);
            }
            (And(l), Right) | (Or(l), Left) => {
                if l.iter()
                    .any(|p| p.is_atom() && seq.contains(&FormulaExtended::init(p, side)))
                {
                    redundant_i += 1;
                    seqs.push(seq);
                    continue 'outer;
                }
                let (p, l) = l.split_first().unwrap();
                for p in l.iter().rev() {
                    let p = FormulaExtended::init(p, side);
                    if !seq.is_trivial(p) {
                        let mut seq = seq.clone();
                        seq.push(p);
                        seqs.push(seq);
                    }
                }
                let p = FormulaExtended::init(p, side);
                if !seq.is_trivial(p) {
                    seq.push(p);
                    seqs.push(seq);
                }
            }
            (To(p, q), Left) => {
                let p = FormulaExtended::init(p, Right);
                let q = FormulaExtended::init(q, Left);
                if q.is_atom() && seq.contains(&q) {
                    redundant_i += 1;
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
                let p = FormulaExtended::init(p, Left);
                let q = FormulaExtended::init(q, Right);
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
                let p_r = FormulaExtended::init(p, Right);
                let q_r = FormulaExtended::init(q, Right);
                if !seq.is_trivial(p_r) && !seq.is_trivial(q_r) {
                    let mut seq = seq.clone();
                    seq.push(p_r);
                    seq.push(q_r);
                    seqs.push(seq);
                }
                let p_l = FormulaExtended::init(p, Left);
                let q_l = FormulaExtended::init(q, Left);
                if !seq.is_trivial(p_l) && !seq.is_trivial(q_l) {
                    seq.push(p_l);
                    seq.push(q_l);
                    seqs.push(seq);
                }
            }
            (Iff(p, q), Right) => {
                let p_r = FormulaExtended::init(p, Right);
                let q_l = FormulaExtended::init(q, Left);
                if !(seq.is_trivial(p_r) || seq.is_trivial(q_l)) {
                    let mut seq = seq.clone();
                    seq.push(p_r);
                    seq.push(q_l);
                    seqs.push(seq);
                }
                let p_l = FormulaExtended::init(p, Left);
                let q_r = FormulaExtended::init(q, Right);
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
    println!("iter: {iter}");
    println!("redundant: {redundant_i}");
    true
}
