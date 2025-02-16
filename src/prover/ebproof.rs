use super::sequent::{
    Sequent,
    Side::{self, Left, Right},
    SidedFormula,
};
use crate::{intern::Names, lang::Formula::*};
use std::{
    fs::File,
    io::{self, BufWriter, Write},
};

use std::{cell::OnceCell, fmt};

#[derive(Clone, Debug)]
pub enum Tactic {
    Axiom,
    Not { side: Side },
    And { side: Side, children_cnt: usize },
    Or { side: Side, children_cnt: usize },
    To { side: Side },
    Iff { side: Side },
    All { side: Side },
    Ex { side: Side },
}

impl Tactic {
    #[inline(always)]
    pub fn children_cnt(&self) -> usize {
        use Tactic::*;
        match self {
            Axiom => 0,
            Not { .. } | All { .. } | Ex { .. } => 1,
            And { children_cnt, .. } | Or { children_cnt, .. } => *children_cnt,
            To { .. } | Iff { .. } => 2,
        }
    }
}

impl fmt::Display for Tactic {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Tactic::*;
        match self {
            Axiom => write!(f, "Axiom"),
            Not { side } => write!(f, r"$\lnot$: {side}"),
            And { side, .. } => write!(f, r"$\land$: {side}"),
            Or { side, .. } => write!(f, r"$\lor$: {side}"),
            To { side } => write!(f, r"$\rightarrow$: {side}"),
            Iff { side } => write!(f, r"$\leftrightarrow$: {side}"),
            All { side } => write!(f, r"$\forall$: {side}"),
            Ex { side } => write!(f, r"$\exists$: {side}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProofNode<'a> {
    pub seq: Sequent<'a>,
    pub tactic: OnceCell<Tactic>,
    pub proved_children_cnt: usize,
    pub parent_idx: Option<usize>,
}

impl<'a> Sequent<'a> {
    #[inline(always)]
    pub fn extended_latex(self, parent_idx: Option<usize>) -> ProofNode<'a> {
        ProofNode {
            seq: self,
            tactic: OnceCell::new(),
            proved_children_cnt: 0,
            parent_idx,
        }
    }
}

fn write_all_proved_seqs(
    nodes: &mut Vec<ProofNode>,
    names: &Names,
    buf: &mut Vec<u8>,
) -> io::Result<()> {
    while let Some(ProofNode {
        seq,
        tactic,
        proved_children_cnt,
        parent_idx,
    }) = nodes.last()
    {
        let Some(tactic) = tactic.get() else {
            // when tactic is not yet initialized
            break;
        };
        if *proved_children_cnt < tactic.children_cnt() {
            // when not all children are processed
            break;
        }
        writeln!(
            buf,
            r"\infer{{{}}}[\scriptsize {tactic}]{{{}}}",
            tactic.children_cnt(),
            seq.display(names)
        )?;
        if let Some(parent_idx) = *parent_idx {
            // when not the root
            // increment the processed children count of the parent
            nodes[parent_idx].proved_children_cnt += 1;
        }
        nodes.pop().unwrap();
    }
    Ok(())
}

fn write_all_seqs(nodes: &mut Vec<ProofNode>, names: &Names, buf: &mut Vec<u8>) -> io::Result<()> {
    while let Some(ProofNode { seq, tactic, .. }) = nodes.pop() {
        if let Some(tactic) = tactic.get() {
            // when has children
            writeln!(
                buf,
                r"\infer{{{}}}[\scriptsize {tactic}]{{{}}}",
                tactic.children_cnt(),
                seq.display(names)
            )?;
        } else {
            // when leaf
            writeln!(buf, r"\hypo{{{}}}", seq.display(names))?;
        }
    }
    Ok(())
}

pub fn ebproof(seq: Sequent, names: &Names) -> io::Result<()> {
    let mut file = BufWriter::new(File::create("out.tex")?);
    writeln!(
        file,
        r"\documentclass[preview,varwidth=\maxdimen,border=10pt]{{standalone}}
\usepackage{{ebproof}}
\begin{{document}}
\begin{{prooftree}}",
    )?;
    const MAX_FILE_SIZE: usize = 1_000_000; // 1MB
    let mut buf: Vec<u8> = Vec::with_capacity(MAX_FILE_SIZE);
    ebproof_core(seq, names, &mut buf)?;
    file.write_all(&buf)?;
    writeln!(
        file,
        r"\end{{prooftree}}
\end{{document}}",
    )?;
    Ok(())
}

pub fn ebproof_core(seq: Sequent, names: &Names, buf: &mut Vec<u8>) -> io::Result<()> {
    if seq.is_initially_trivial() {
        // when trivial from the beginning
        writeln!(
            buf,
            r"\infer{{0}}[\scriptsize Axiom]{{{}}}",
            seq.display(names)
        )?;
        return Ok(());
    }
    let mut nodes = vec![seq.extended_latex(None)];
    'outer: loop {
        // write all proved sequents
        write_all_proved_seqs(&mut nodes, names, buf)?;
        // get the last sequent
        let Some(ProofNode { seq, tactic, .. }) = nodes.last() else {
            // if no sequent to be proved, completed the proof
            return Ok(());
        };
        let mut seq = seq.clone();
        // get the last formula
        let Some(SidedFormula { fml, side }) = seq.pop() else {
            // if `seq` has no formula, it is impossible to prove
            // this could happen: ex. `true ⊢`, `⊢ false` goes to `⊢`
            // write all sequents
            write_all_seqs(&mut nodes, names, buf)?;
            return Ok(());
        };
        match (fml, side) {
            // Convert `¬p ⊢` to `⊢ p`
            // Convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                // set the tactic
                tactic.set(Tactic::Not { side }).unwrap();
                let p = p.with_side(side.opposite());
                let is_trivial = seq.is_trivial(p);
                seq.push(p);
                let seq = seq.extended_latex(Some(nodes.len() - 1));
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    seq.tactic.set(Tactic::Axiom).unwrap();
                }
                nodes.push(seq);
            }
            // Convert `p ∧ q ∧ r ⊢` to `p, q, r ⊢`
            // Convert `⊢ p ∨ q ∨ r` to `⊢ p, q, r`
            (And(l), Left) | (Or(l), Right) => {
                // set the tactic
                let init = match side {
                    Left => Tactic::And {
                        side,
                        children_cnt: 1,
                    },
                    Right => Tactic::Or {
                        side,
                        children_cnt: 1,
                    },
                };
                tactic.set(init).unwrap();
                let mut is_trivial = false;
                for p in l {
                    let p = p.with_side(side);
                    if seq.is_trivial(p) {
                        is_trivial = true;
                    }
                    seq.push(p);
                }
                let seq = seq.extended_latex(Some(nodes.len() - 1));
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    seq.tactic.set(Tactic::Axiom).unwrap();
                }
                nodes.push(seq);
            }
            // Convert `p ∨ q ∨ r ⊢` to `p ⊢` and `q ⊢` and `r ⊢`
            // Convert `⊢ p ∧ q ∧ r` to `⊢ p` and `⊢ q` and `⊢ r`
            (And(l), Right) | (Or(l), Left) => {
                if l.iter()
                    .map(|p| p.with_side(side))
                    .any(|p| p.is_atom() && seq.contains(&p))
                {
                    // when `fml` is redundant
                    // ex. `p ∨ q ∨ r, p ⊢`
                    // ex. `⊢ p ∧ q ∧ r, p`
                    // drop `fml` and continue to the next sequent
                    nodes.last_mut().unwrap().seq.pop();
                    continue 'outer;
                }
                // TODO: 2025/02/13 if l is empty, set the Axiom tactic
                // set the tactic
                let init = match side {
                    Right => Tactic::And {
                        side,
                        children_cnt: l.len(),
                    },
                    Left => Tactic::Or {
                        side,
                        children_cnt: l.len(),
                    },
                };
                tactic.set(init).unwrap();
                let parent_idx = nodes.len() - 1;
                for p in l.iter().rev() {
                    let p = p.with_side(side);
                    let is_trivial = seq.is_trivial(p);
                    let mut seq = seq.clone();
                    seq.push(p);
                    let seq = seq.extended_latex(Some(parent_idx));
                    if is_trivial {
                        // if trivial, set the Axiom tactic
                        seq.tactic.set(Tactic::Axiom).unwrap();
                    }
                    nodes.push(seq);
                }
            }
            // Convert `p → q ⊢` to `⊢ p` and `q ⊢`
            (To(p, q), Left) => {
                let q = q.with_side(Left);
                if q.is_atom() && seq.contains(&q) {
                    // when `fml` is redundant
                    // ex. `p → q, q ⊢`
                    // drop `fml` and continue to the next sequent
                    nodes.last_mut().unwrap().seq.pop();
                    continue 'outer;
                }
                // set the tactic
                tactic.set(Tactic::To { side }).unwrap();
                let p = p.with_side(Right);
                let is_trivial_q = seq.is_trivial(q);
                let is_trivial_p = seq.is_trivial(p);
                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(q);
                seq2.push(p);
                let parent_idx = nodes.len() - 1;
                let seq1 = seq1.extended_latex(Some(parent_idx));
                let seq2 = seq2.extended_latex(Some(parent_idx));
                if is_trivial_q {
                    // if trivial, set the Axiom tactic
                    seq1.tactic.set(Tactic::Axiom).unwrap();
                }
                if is_trivial_p {
                    // if trivial, set the Axiom tactic
                    seq2.tactic.set(Tactic::Axiom).unwrap();
                }
                nodes.push(seq1);
                nodes.push(seq2);
            }
            // Convert `⊢ p → q` to `p ⊢ q`
            (To(p, q), Right) => {
                // set the tactic
                tactic.set(Tactic::To { side }).unwrap();
                let p = p.with_side(Left);
                let q = q.with_side(Right);
                let is_trivial = seq.is_trivial2(p, q);
                seq.push(p);
                seq.push(q);
                let seq = seq.extended_latex(Some(nodes.len() - 1));
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    seq.tactic.set(Tactic::Axiom).unwrap();
                }
                nodes.push(seq);
            }
            // Convert `p ↔ q ⊢` to `p, q ⊢` and `⊢ p, q`
            // Convert `⊢ p ↔ q` to `p ⊢ q` and `q ⊢ p`
            (Iff(p, q), side) => {
                // set the tactic
                tactic.set(Tactic::Iff { side }).unwrap();
                let p_l = p.with_side(Left);
                let p_r = p.with_side(Right);
                let q_l = q.with_side(Left);
                let q_r = q.with_side(Right);
                let (fml11, fml12, fml21, fml22) = match side {
                    Left => (p_r, q_r, p_l, q_l),
                    Right => (q_l, p_r, p_l, q_r),
                };
                let is_trivial_1 = seq.is_trivial2(fml11, fml12);
                let is_trivial_2 = seq.is_trivial2(fml21, fml22);
                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(fml11);
                seq1.push(fml12);
                seq2.push(fml21);
                seq2.push(fml22);
                let parent_idx = nodes.len() - 1;
                let seq1 = seq1.extended_latex(Some(parent_idx));
                let seq2 = seq2.extended_latex(Some(parent_idx));
                if is_trivial_1 {
                    // if trivial, set the Axiom tactic
                    seq1.tactic.set(Tactic::Axiom).unwrap();
                }
                if is_trivial_2 {
                    // if trivial, set the Axiom tactic
                    seq2.tactic.set(Tactic::Axiom).unwrap();
                }
                nodes.push(seq1);
                nodes.push(seq2);
            }
            (Pred(_, _), _) => {
                // since formulas in 'seq' are ordered,
                // if `fml` is predicate, no formulas can be processed
                // thus, it is impossible to prove
                // write all sequents
                write_all_seqs(&mut nodes, names, buf)?;
                return Ok(());
            }
            (Ex(_, _) | All(_, _), _) => unimplemented!(),
        }
    }
}
