use super::sequent::{
    Sequent,
    Side::{self, Left, Right},
    SidedFormula,
};
use crate::{intern::Names, lang::Formula::*};
use log::error;
use std::{cell::OnceCell, fmt, fs::File, io::Write, path::PathBuf};

const MAX_FILE_SIZE: usize = 1_000_000; // 1MB

#[derive(Clone, Debug)]
enum Tactic {
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
    fn children_cnt(&self) -> usize {
        use Tactic::*;
        match self {
            Axiom => 0,
            Not { .. } | All { .. } | Ex { .. } | To { side: Right } => 1,
            And { children_cnt, .. } | Or { children_cnt, .. } => *children_cnt,
            To { side: Left } | Iff { .. } => 2,
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
            To { side } => write!(f, r"$\lif$: {side}"),
            Iff { side } => write!(f, r"$\liff$: {side}"),
            All { side } => write!(f, r"$\lall$: {side}"),
            Ex { side } => write!(f, r"$\lis$: {side}"),
        }
    }
}

#[derive(Clone, Debug)]
struct ProofNode<'a> {
    seq: Sequent<'a>,
    tactic: OnceCell<Tactic>,
    proved_children_cnt: usize,
    parent_idx: Option<usize>,
}

impl<'a> ProofNode<'a> {
    #[inline(always)]
    fn new_root(seq: Sequent<'a>) -> Self {
        Self {
            seq,
            tactic: OnceCell::new(),
            proved_children_cnt: 0,
            parent_idx: None,
        }
    }
}

impl<'a> Sequent<'a> {
    // TODO: 2025/05/30 forestを参考にするか
    #[inline(always)]
    fn into_node(self, parent_idx: usize) -> ProofNode<'a> {
        ProofNode {
            seq: self,
            tactic: OnceCell::new(),
            proved_children_cnt: 0,
            parent_idx: Some(parent_idx),
        }
    }
}

/// Generates a LaTeX proof tree using the ebproof package.
pub fn ebproof(seq: Sequent, names: &Names, out: &str) {
    // buffer for storing the proof tree string
    let mut buf: Vec<u8> = Vec::with_capacity(MAX_FILE_SIZE);
    // generate the proof tree
    ebproof_impl(seq, names, &mut buf);
    // create output LaTeX file
    let mut file = File::create(PathBuf::from(out).join("ebproof.tex")).unwrap();
    // replace the placeholder with proof
    let proof = include_str!("../../templates/ebproof.tex")
        .replace("%PROOF_CONTENT%", String::from_utf8_lossy(&buf).trim());
    // write proof
    file.write_all(proof.as_bytes()).unwrap();
}

/// Implementation for generating LaTeX proof trees.
fn ebproof_impl(seq: Sequent, names: &Names, buf: &mut Vec<u8>) {
    if seq.is_initially_trivial() {
        // trivial from the beginning
        // ex. p, q ⊢ r, p
        writeln!(
            buf,
            r"\infer{{0}}[\scriptsize Axiom]{{{}}}",
            seq.display(names)
        )
        .unwrap();
        return;
    }
    let mut nodes = vec![ProofNode::new_root(seq)];
    'main: loop {
        // write all proved nodes
        flush_proved_nodes(&mut nodes, names, buf);
        // get the last sequent
        let Some(ProofNode { seq, tactic, .. }) = nodes.last() else {
            // if no sequent to be proved, completed the proof
            return;
        };
        let mut seq = seq.clone();
        // get the last formula
        let SidedFormula { fml, side } = seq.pop().unwrap();
        match (fml, side) {
            // Convert `¬p ⊢` to `⊢ p`
            // Convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                // set the tactic
                tactic.set(Tactic::Not { side }).unwrap();
                let p = p.with_side(side.opposite());
                let is_trivial = seq.is_trivial(p);
                seq.push(p);
                let parent_idx = nodes.len() - 1;
                let node = seq.into_node(parent_idx);
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    node.tactic.set(Tactic::Axiom).unwrap();
                }
                nodes.push(node);
            }
            // Convert `p ∧ q ∧ r ⊢` to `p, q, r ⊢`
            // Convert `⊢ p ∨ q ∨ r` to `⊢ p, q, r`
            (And(l), Left) | (Or(l), Right) => {
                // set the tactic
                let initial_tactic = match side {
                    Left => Tactic::And {
                        side,
                        children_cnt: 1,
                    },
                    Right => Tactic::Or {
                        side,
                        children_cnt: 1,
                    },
                };
                tactic.set(initial_tactic).unwrap();
                let mut is_trivial = false;
                for p in l {
                    let p = p.with_side(side);
                    if seq.is_trivial(p) {
                        is_trivial = true;
                    }
                    seq.push(p);
                }
                let parent_idx = nodes.len() - 1;
                let seq = seq.into_node(parent_idx);
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
                    .any(|p| p.is_atom() && seq.contains_atom(&p))
                {
                    // when `fml` is redundant
                    // ex. `p ∨ q ∨ r, p ⊢`
                    // ex. `⊢ p ∧ q ∧ r, p`
                    // drop `fml` and continue to the next sequent
                    nodes.last_mut().unwrap().seq.pop();
                    continue 'main;
                }
                // TODO: 2025/02/13 if l is empty, set the Axiom tactic
                // set the tactic
                let initial_tactic = match side {
                    Right => Tactic::And {
                        side,
                        children_cnt: l.len(),
                    },
                    Left => Tactic::Or {
                        side,
                        children_cnt: l.len(),
                    },
                };
                tactic.set(initial_tactic).unwrap();
                let parent_idx = nodes.len() - 1;
                for p in l.iter().rev() {
                    let p = p.with_side(side);
                    let is_trivial = seq.is_trivial(p);
                    let mut seq = seq.clone();
                    seq.push(p);
                    let seq = seq.into_node(parent_idx);
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
                // check if `fml` is redundant
                if q.is_atom() && seq.contains_atom(&q) {
                    // ex. `p → q, q ⊢`
                    // drop this `fml` and continue to the next sequent
                    nodes.last_mut().unwrap().seq.pop();
                    continue 'main;
                }
                // set the tactic
                tactic.set(Tactic::To { side }).unwrap();
                let p = p.with_side(Right);
                let is_trivial_p = seq.is_trivial(p);
                let is_trivial_q = seq.is_trivial(q);
                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(p);
                seq2.push(q);
                let parent_idx = nodes.len() - 1;
                let node1 = seq1.into_node(parent_idx);
                let node2 = seq2.into_node(parent_idx);
                if is_trivial_p {
                    // if trivial, set the Axiom tactic
                    node1.tactic.set(Tactic::Axiom).unwrap();
                }
                if is_trivial_q {
                    // if trivial, set the Axiom tactic
                    node2.tactic.set(Tactic::Axiom).unwrap();
                }
                // we need to process `node1` first, so push `node1` later
                nodes.push(node2);
                nodes.push(node1);
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
                let parent_idx = nodes.len() - 1;
                let node = seq.into_node(parent_idx);
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    node.tactic.set(Tactic::Axiom).unwrap();
                }
                nodes.push(node);
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
                    Left => (p_l, q_l, p_r, q_r),
                    Right => (p_l, q_r, q_l, p_r),
                };
                let is_trivial1 = seq.is_trivial2(fml11, fml12);
                let is_trivial2 = seq.is_trivial2(fml21, fml22);
                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(fml11);
                seq1.push(fml12);
                seq2.push(fml21);
                seq2.push(fml22);
                let parent_idx = nodes.len() - 1;
                let node1 = seq1.into_node(parent_idx);
                let node2 = seq2.into_node(parent_idx);
                if is_trivial1 {
                    // if trivial, set the Axiom tactic
                    node1.tactic.set(Tactic::Axiom).unwrap();
                }
                if is_trivial2 {
                    // if trivial, set the Axiom tactic
                    node2.tactic.set(Tactic::Axiom).unwrap();
                }
                // we need to process `node1` first, so push `node1` later
                nodes.push(node2);
                nodes.push(node1);
            }
            (Pred(..), _) => unreachable!(),
            (Ex(..) | All(..), _) => unimplemented!(),
        }
    }
}

/// Writes all proved nodes to the LaTeX buffer.
/// - Processes only when all their children are proved
/// - Automatically increments parent nodes' count of proved children
fn flush_proved_nodes(nodes: &mut Vec<ProofNode>, names: &Names, buf: &mut Vec<u8>) {
    while let Some(ProofNode {
        seq,
        tactic,
        proved_children_cnt,
        parent_idx,
    }) = nodes.last()
    {
        let Some(tactic) = tactic.get() else {
            // tactic not initialized yet
            break;
        };
        if *proved_children_cnt < tactic.children_cnt() {
            // some children are not yet proved
            break;
        }
        // check if the buffer size exceeds the limit
        if buf.len() > MAX_FILE_SIZE {
            // terminate the entire process immediately
            error!("Failed: File size exceeded the limit.");
            panic!("File size exceeded the limit.");
        }
        // write the inference rule
        writeln!(
            buf,
            r"\infer{{{}}}[\scriptsize {tactic}]{{{}}}",
            tactic.children_cnt(),
            seq.display(names)
        )
        .unwrap();
        if let Some(parent_idx) = *parent_idx {
            // if has a parent
            // increment parent's proved children count
            nodes[parent_idx].proved_children_cnt += 1;
        }
        // remove the written node
        nodes.pop().unwrap();
    }
}

/// Writes all remaining nodes to the LaTeX buffer.
/// When proof construction fails (e.g., when encountering atomic formulas,
/// which cannot be processed further), this function writes the current state of the
/// proof tree to give users insight into where and why the proof attempt failed.
/// - Non-leaf nodes: Written as inference rules
/// - Leaf nodes: Written as hypotheses
fn flush_all_nodes(nodes: &mut Vec<ProofNode>, names: &Names, buf: &mut Vec<u8>) {
    while let Some(ProofNode { seq, tactic, .. }) = nodes.pop() {
        // check if the buffer size exceeds the limit
        if buf.len() > MAX_FILE_SIZE {
            // terminate the entire process immediately
            error!("Failed: File size exceeded the limit.");
            panic!("File size exceeded the limit.");
        }
        if let Some(tactic) = tactic.get() {
            // when it has children
            // write the inference rule
            writeln!(
                buf,
                r"\infer{{{}}}[\scriptsize {tactic}]{{{}}}",
                tactic.children_cnt(),
                seq.display(names)
            )
            .unwrap();
        } else {
            // when it is leaf
            // write the sequent as a hypothesis
            writeln!(buf, r"\hypo{{{}}}", seq.display(names)).unwrap();
        }
    }
}
