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
        writeln!(file, r"\hypo{{{}}}", seq.display(names).to_latex())?;
        return Ok(true);
    };
    let mut seqs = vec![seq.extended_latex(None)];
    'outer: loop {
        // write all proved sequents
        write_all_proved_seqs(&mut seqs, names, file)?;
        // get the last sequent
        let Some(SequentExtendedLatex {
            seq,
            tactic,
            processed_children_cnt,
            parent_idx,
        }) = seqs.last()
        else {
            // if no sequent to be proved, completed the proof
            return Ok(true);
        };
        // get the last formula
        let Some(FormulaExtended { fml, side }) = seq.last() else {
            // if no formula to be processed, failed to prove
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
                    // if the sequent is trivial, set the Axiom tactic
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
                    // if the sequent is trivial, set the Axiom tactic
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
                    // drop `fml` and continue to the next sequent
                    seqs.last_mut().unwrap().seq.pop();
                    continue 'outer;
                }
                let mut l = l.iter().map(|p| p.extended(*side)).rev().peekable();
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
                        // if the sequent is trivial, drop it and continue to the next sequent
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
                let p = p.extended(Left);
                let q = q.extended(Right);
                if seq.is_trivial2(p, q) {
                    // if the sequent is trivial, drop it and continue to the next sequent
                    seqs.pop().unwrap();
                    continue 'outer;
                }
                seq.push(p);
                seq.push(q);
            }
            // Convert `p ↔ q ⊢` to `p, q ⊢` and `⊢ p, q`
            // Convert `⊢ p ↔ q` to `p ⊢ q` and `q ⊢ p`
            (Iff(p, q), side) => {
                let p_l = p.extended(Left);
                let p_r = p.extended(Right);
                let q_l = q.extended(Left);
                let q_r = q.extended(Right);
                let (fml11, fml12, fml21, fml22) = match side {
                    Left => (p_l, q_l, p_r, q_r),
                    Right => (p_l, q_r, q_l, p_r),
                };
                match (seq.is_trivial2(fml11, fml12), seq.is_trivial2(fml21, fml22)) {
                    (true, true) => {
                        // if the sequent is trivial, drop it
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
                        seq.push(fml21);
                        seq.push(fml22);
                        seq2.push(fml11);
                        seq2.push(fml12);
                        seqs.push(seq2);
                    }
                }
            }
            (Pred(_, _), _) => return Ok(false),
            (Ex(_, _) | All(_, _), _) => unimplemented!(),
        }
    }
}
