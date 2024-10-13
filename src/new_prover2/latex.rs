use crate::lang::{Formula::*, Sequent};
use crate::name::Names;
use crate::new_prover2::lang::Side::{Left, Right};
use crate::new_prover2::lang::{FormulaExtended, SequentExtendedLatex};
use std::io::Write;
use std::{fs, io};

fn write_all_proved_seqs(
    seqs: &mut Vec<SequentExtendedLatex>,
    names: &Names,
    file: &mut io::BufWriter<fs::File>,
) -> io::Result<()> {
    while let Some(SequentExtendedLatex {
        seq,
        tactic,
        processed_children_cnt,
        parent_idx,
    }) = seqs.last()
    {
        let Some((children_cnt, label)) = tactic.get() else {
            // when tactic is not yet initialized
            break;
        };
        if processed_children_cnt < children_cnt {
            // when not all children are processed
            break;
        }
        writeln!(
            file,
            r"\infer{{{children_cnt}}}[\scriptsize {label}]{{{}}}",
            seq.to_seq().display(names).to_latex()
        )?;
        if let Some(parent_idx) = *parent_idx {
            // when not the root
            // increment the processed children count of the parent
            seqs[parent_idx].processed_children_cnt += 1;
        }
        seqs.pop().unwrap();
    }
    Ok(())
}

fn write_all_seqs(
    seqs: &mut Vec<SequentExtendedLatex>,
    names: &Names,
    file: &mut io::BufWriter<fs::File>,
) -> io::Result<()> {
    while let Some(SequentExtendedLatex { seq, tactic, .. }) = seqs.pop() {
        if let Some((children_cnt, label)) = tactic.get() {
            // when has children
            writeln!(
                file,
                r"\infer{{{children_cnt}}}[\scriptsize {label}]{{{}}}",
                seq.to_seq().display(names).to_latex()
            )?;
        } else {
            // when leaf
            writeln!(file, r"\hypo{{{}}}", seq.to_seq().display(names).to_latex())?;
        }
    }
    Ok(())
}

fn latex_sequent_calculus(
    seq: &Sequent,
    names: &Names,
    file: &mut io::BufWriter<fs::File>,
) -> io::Result<bool> {
    let Some(seq) = seq.extended() else {
        // when trivial from the beginning
        writeln!(
            file,
            r"\infer{{1}}[\scriptsize Axiom]{{{}}}",
            seq.display(names).to_latex()
        )?;
        return Ok(true);
    };
    let mut seqs = vec![seq.extended_latex(None)];
    'outer: loop {
        // write all proved sequents
        write_all_proved_seqs(&mut seqs, names, file)?;
        // get the last sequent
        let Some(SequentExtendedLatex { seq, tactic, .. }) = seqs.last() else {
            // if no sequent to be proved, completed the proof
            return Ok(true);
        };
        // get the last formula
        let Some(FormulaExtended { fml, side }) = seq.last() else {
            // if `seq` has no formula, it is impossible to prove
            // this could happen: ex. `true ⊢`, `⊢ false` goes to `⊢`
            // write all sequents
            write_all_seqs(&mut seqs, names, file)?;
            return Ok(false);
        };
        match (fml, side) {
            // Convert `¬p ⊢` to `⊢ p`
            // Convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                // set the tactic
                tactic.set((1, fml.get_label(*side))).unwrap();
                let p = p.extended(side.opposite());
                let is_trivial = seq.is_trivial(p);
                let mut seq = seq.clone();
                seq.push(p);
                let seq = seq.extended_latex(Some(seqs.len() - 1));
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    seq.tactic.set((0, "Axiom".into())).unwrap();
                }
                seqs.push(seq);
            }
            // Convert `p ∧ q ∧ r ⊢` to `p, q, r ⊢`
            // Convert `⊢ p ∨ q ∨ r` to `⊢ p, q, r`
            (And(l), Left) | (Or(l), Right) => {
                // set the tactic
                tactic.set((1, fml.get_label(*side))).unwrap();
                let mut is_trivial = false;
                let mut seq = seq.clone();
                for p in l {
                    let p = p.extended(*side);
                    if seq.is_trivial(p) {
                        is_trivial = true;
                    }
                    seq.push(p);
                }
                let seq = seq.extended_latex(Some(seqs.len() - 1));
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    seq.tactic.set((0, "Axiom".into())).unwrap();
                }
                seqs.push(seq);
            }
            // Convert `p ∨ q ∨ r ⊢` to `p ⊢` and `q ⊢` and `r ⊢`
            // Convert `⊢ p ∧ q ∧ r` to `⊢ p` and `⊢ q` and `⊢ r`
            (And(l), Right) | (Or(l), Left) => {
                if l.iter()
                    .map(|p| p.extended(*side))
                    .any(|p| p.is_atom() && seq.contains(&p))
                {
                    // when `fml` is redundant
                    // ex. `p ∨ q ∨ r, p ⊢`
                    // ex. `⊢ p ∧ q ∧ r, p`
                    // drop `fml` and continue to the next sequent
                    seqs.last_mut().unwrap().seq.pop();
                    continue 'outer;
                }
                // set the tactic
                tactic.set((l.len(), fml.get_label(*side))).unwrap();
                for p in l.iter().rev() {
                    let p = p.extended(*side);
                    let is_trivial = seq.is_trivial(p);
                    let mut seq = seq.clone();
                    seq.push(p);
                    let seq = seq.extended_latex(Some(seqs.len() - 1));
                    if is_trivial {
                        // if trivial, set the Axiom tactic
                        seq.tactic.set((0, "Axiom".into())).unwrap();
                    }
                    seqs.push(seq);
                }
            }
            // Convert `p → q ⊢` to `⊢ p` and `q ⊢`
            (To(p, q), Left) => {
                let q = q.extended(Left);
                if q.is_atom() && seq.contains(&q) {
                    // when `fml` is redundant
                    // ex. `p → q, q ⊢`
                    // drop `fml` and continue to the next sequent
                    seqs.last_mut().unwrap().seq.pop();
                    continue 'outer;
                }
                // set the tactic
                tactic.set((2, fml.get_label(*side))).unwrap();
                let p = p.extended(Right);
                let is_trivial_q = seq.is_trivial(q);
                let is_trivial_p = seq.is_trivial(p);
                let mut seq1 = seq.clone();
                let mut seq2 = seq.clone();
                seq1.push(q);
                seq2.push(p);
                let seq1 = seq1.extended_latex(Some(seqs.len() - 1));
                let seq2 = seq2.extended_latex(Some(seqs.len() - 1));
                if is_trivial_q {
                    // if trivial, set the Axiom tactic
                    seq1.tactic.set((0, "Axiom".into())).unwrap();
                }
                if is_trivial_p {
                    // if trivial, set the Axiom tactic
                    seq2.tactic.set((0, "Axiom".into())).unwrap();
                }
                seqs.push(seq1);
                seqs.push(seq2);
            }
            // Convert `⊢ p → q` to `p ⊢ q`
            (To(p, q), Right) => {
                // set the tactic
                tactic.set((1, fml.get_label(*side))).unwrap();
                let p = p.extended(Left);
                let q = q.extended(Right);
                let is_trivial = seq.is_trivial2(p, q);
                let mut seq = seq.clone();
                seq.push(p);
                seq.push(q);
                let seq = seq.extended_latex(Some(seqs.len() - 1));
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    seq.tactic.set((0, "Axiom".into())).unwrap();
                }
                seqs.push(seq);
            }
            // Convert `p ↔ q ⊢` to `p, q ⊢` and `⊢ p, q`
            // Convert `⊢ p ↔ q` to `p ⊢ q` and `q ⊢ p`
            (Iff(p, q), side) => {
                // set the tactic
                tactic.set((2, fml.get_label(*side))).unwrap();
                let p_l = p.extended(Left);
                let p_r = p.extended(Right);
                let q_l = q.extended(Left);
                let q_r = q.extended(Right);
                let (fml11, fml12, fml21, fml22) = match side {
                    Left => (p_r, q_r, p_l, q_l),
                    Right => (q_l, p_r, p_l, q_r),
                };
                let is_trivial_1 = seq.is_trivial2(fml11, fml12);
                let is_trivial_2 = seq.is_trivial2(fml21, fml22);
                let mut seq1 = seq.clone();
                let mut seq2 = seq.clone();
                seq1.push(fml11);
                seq1.push(fml12);
                seq2.push(fml21);
                seq2.push(fml22);
                let seq1 = seq1.extended_latex(Some(seqs.len() - 1));
                let seq2 = seq2.extended_latex(Some(seqs.len() - 1));
                if is_trivial_1 {
                    // if trivial, set the Axiom tactic
                    seq1.tactic.set((0, "Axiom".into())).unwrap();
                }
                if is_trivial_2 {
                    // if trivial, set the Axiom tactic
                    seq2.tactic.set((0, "Axiom".into())).unwrap();
                }
                seqs.push(seq1);
                seqs.push(seq2);
            }
            (Pred(_, _), _) => {
                // since formulas in 'seq' are ordered,
                // if `fml` is predicate, no formulas can be processed
                // thus, it is impossible to prove
                // write all sequents
                write_all_seqs(&mut seqs, names, file)?;
                return Ok(false);
            }
            (Ex(_, _) | All(_, _), _) => unimplemented!(),
        }
    }
}
