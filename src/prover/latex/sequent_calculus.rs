use crate::{
    app::{LatexError, MAX_OUTPUT_SIZE},
    core::{names::Names, syntax::Formula::*},
    prover::sequent::{
        Sequent,
        Side::{self, Left, Right},
        SidedFormula,
    },
};
use Latex::*;
use log::warn;
use std::{cell::OnceCell, fmt, fs::File, io::Write, path::PathBuf};

/// Represents different LaTeX packages.
#[derive(Clone, Copy, Debug)]
pub enum Latex {
    /// Use the ebproof package
    Ebproof,
    /// Use the bussproofs package
    Bussproofs,
}

#[derive(Clone, Debug)]
enum Tactic {
    Axiom,
    Not { side: Side },
    And { side: Side, children_cnt: usize },
    Or { side: Side, children_cnt: usize },
    To { side: Side },
    Iff { side: Side },
    // All { side: Side },
    // Ex { side: Side },
}

impl Tactic {
    #[inline(always)]
    const fn children_cnt(&self) -> usize {
        use Tactic::*;
        match self {
            Axiom => 0,
            Not { .. } | To { side: Right } /*| All { .. } | Ex { .. }*/ => 1,
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
            // All { side } => write!(f, r"$\lall$: {side}"),
            // Ex { side } => write!(f, r"$\lis$: {side}"),
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
    const fn new_root(seq: Sequent<'a>) -> Self {
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
    const fn into_node(self, parent_idx: usize) -> ProofNode<'a> {
        ProofNode {
            seq: self,
            tactic: OnceCell::new(),
            proved_children_cnt: 0,
            parent_idx: Some(parent_idx),
        }
    }
}

/// Generates a LaTeX proof tree using sequent calculus.
pub fn sequent_calculus(
    seq: Sequent,
    names: &Names,
    out: &str,
    latex: Latex,
) -> Result<(), LatexError> {
    // create proof tree in LaTeX
    let proof = sequent_calculus_impl(seq, names, latex)?;
    // replace turnstile symbol based on LaTeX package
    let proof = String::from_utf8_lossy(&proof).replace(
        r"\vdash",
        match latex {
            Ebproof => r"&\vdash",
            Bussproofs => r"\fCenter",
        },
    );
    // embed proof into LaTeX template
    let template = match latex {
        Ebproof => include_str!("../../../templates/ebproof.tex"),
        Bussproofs => include_str!("../../../templates/bussproofs.tex"),
    };
    let proof = template.replace("%PROOF_CONTENT%", proof.trim());
    // save LaTeX file
    let file = match latex {
        Ebproof => "ebproof.tex",
        Bussproofs => "bussproofs.tex",
    };
    let mut file = File::create(PathBuf::from(out).join(file)).unwrap();
    file.write_all(proof.as_bytes()).unwrap();
    Ok(())
}

/// Implementation for generating LaTeX proof trees.
fn sequent_calculus_impl(seq: Sequent, names: &Names, latex: Latex) -> Result<Vec<u8>, LatexError> {
    // buffer for storing the proof tree string
    let mut buf: Vec<u8> = Vec::with_capacity(MAX_OUTPUT_SIZE);
    if seq.is_initially_trivial() {
        // trivial from the beginning
        // ex. p, q ⊢ r, p
        match latex {
            Ebproof => {
                writeln!(
                    buf,
                    r"\infer{{0}}[\scriptsize Axiom]{{{}}}",
                    seq.display(names)
                )
                .unwrap();
            }
            Bussproofs => {
                writeln!(buf, r"\AxiomC{{}}").unwrap();
                writeln!(buf, r"\RightLabel{{\scriptsize Axiom}}").unwrap();
                writeln!(buf, r"\UnaryInf${}$", seq.display(names)).unwrap();
            }
        }
        return Ok(buf);
    }
    let mut nodes = vec![ProofNode::new_root(seq)];
    'main: loop {
        // write all proved nodes
        flush_proved_nodes(&mut nodes, names, &mut buf, latex)?;
        // get the last sequent
        let Some(ProofNode { seq, tactic, .. }) = nodes.last() else {
            // if no sequent to be proved, completed the proof
            return Ok(buf);
        };
        let mut seq = seq.clone();
        // get the last formula
        // safe unwrap: provable sequents contain processable formulas
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
            // Drop `true` or `false` in `true ⊢` or `⊢ false`
            (And(l), Left) | (Or(l), Right) => {
                if l.is_empty() {
                    // `true ⊢` and `⊢ false`
                    // avoid showing trivial true/false elimination step
                    // drop `fml` and continue to the next sequent
                    nodes.last_mut().unwrap().seq.pop();
                    continue 'main;
                }
                // set the tactic
                let tactic_to_apply = match side {
                    Left => Tactic::And {
                        side,
                        children_cnt: 1,
                    },
                    Right => Tactic::Or {
                        side,
                        children_cnt: 1,
                    },
                };
                tactic.set(tactic_to_apply).unwrap();
                let mut is_trivial = false;
                for p in l {
                    let p = p.with_side(side);
                    if seq.is_trivial(p) {
                        is_trivial = true;
                    }
                    seq.push(p);
                }
                let parent_idx = nodes.len() - 1;
                let node = seq.into_node(parent_idx);
                if is_trivial {
                    // if trivial, set the Axiom tactic
                    node.tactic.set(Tactic::Axiom).unwrap();
                }
                nodes.push(node);
            }
            // Convert `p ∨ q ∨ r ⊢` to `p ⊢` and `q ⊢` and `r ⊢`
            // Convert `⊢ p ∧ q ∧ r` to `⊢ p` and `⊢ q` and `⊢ r`
            // Set Axiom tactic for `⊢ true` and `false ⊢`
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
                // set the tactic
                let tactic_to_apply = if l.is_empty() {
                    // `⊢ true` and `false ⊢`
                    Tactic::Axiom
                } else {
                    match side {
                        Right => Tactic::And {
                            side,
                            children_cnt: l.len(),
                        },
                        Left => Tactic::Or {
                            side,
                            children_cnt: l.len(),
                        },
                    }
                };
                tactic.set(tactic_to_apply).unwrap();
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
fn flush_proved_nodes(
    nodes: &mut Vec<ProofNode>,
    names: &Names,
    buf: &mut Vec<u8>,
    latex: Latex,
) -> Result<(), LatexError> {
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
        if buf.len() > MAX_OUTPUT_SIZE {
            warn!("Failed: File size exceeded the limit.");
            return Err(LatexError::OutputTooLarge);
        }
        // write the inference rule
        match latex {
            Ebproof => {
                writeln!(
                    buf,
                    r"\infer{{{}}}[\scriptsize {tactic}]{{{}}}",
                    tactic.children_cnt(),
                    seq.display(names)
                )
                .unwrap();
            }
            Bussproofs => match tactic.children_cnt() {
                0 => {
                    writeln!(buf, r"\AxiomC{{}}").unwrap();
                    writeln!(buf, r"\RightLabel{{\scriptsize Axiom}}").unwrap();
                    writeln!(buf, r"\UnaryInf${}$", seq.display(names)).unwrap();
                }
                1 => {
                    writeln!(buf, r"\RightLabel{{\scriptsize {tactic}}}").unwrap();
                    writeln!(buf, r"\UnaryInf${}$", seq.display(names)).unwrap();
                }
                2 => {
                    writeln!(buf, r"\RightLabel{{\scriptsize {tactic}}}").unwrap();
                    writeln!(buf, r"\BinaryInf${}$", seq.display(names)).unwrap();
                }
                3 => {
                    writeln!(buf, r"\RightLabel{{\scriptsize {tactic}}}").unwrap();
                    writeln!(buf, r"\TrinaryInf${}$", seq.display(names)).unwrap();
                }
                4 => {
                    writeln!(buf, r"\RightLabel{{\scriptsize {tactic}}}").unwrap();
                    writeln!(buf, r"\QuaternaryInf${}$", seq.display(names)).unwrap();
                }
                5 => {
                    writeln!(buf, r"\RightLabel{{\scriptsize {tactic}}}").unwrap();
                    writeln!(buf, r"\QuinaryInf${}$", seq.display(names)).unwrap();
                }
                _ => {
                    return Err(LatexError::TooManyBranches);
                }
            },
        }
        if let Some(parent_idx) = *parent_idx {
            // if has a parent
            // increment parent's proved children count
            nodes[parent_idx].proved_children_cnt += 1;
        }
        // remove the written node
        nodes.pop().unwrap();
    }
    Ok(())
}
