use super::sequent::{
    Sequent,
    Side::{Left, Right},
    SidedFormula,
};
use crate::{
    intern::Names,
    lang::Formula::{self, *},
};
use log::error;
use rustc_hash::FxHashMap;
use std::{
    cell::OnceCell,
    fs::File,
    io::{self, Write},
    path::PathBuf,
};

const MAX_FILE_SIZE: usize = 1_000_000; // 1MB

/// Internal proof node for processing proof tree generation
#[derive(Clone, Debug)]
struct ProofNode<'a> {
    seq: Sequent<'a>,
    // number of children nodes
    children_cnt: OnceCell<usize>,
    // number of proved children nodes
    proved_children_cnt: usize,
    // None if root node, Some(parent_idx) if not
    parent_idx: Option<usize>,
    // sided formula map with id assignment using FxHashMap for performance
    formula_map: FxHashMap<usize, SidedFormula<'a>>,
    // newly added formulas with their ids
    added_formulas: Vec<(usize, SidedFormula<'a>)>,
    // from information for this node (None for root)
    from: Option<usize>,
}

/// Forest node for LaTeX generation output
#[derive(Clone, Debug)]
struct ForestNode<'a> {
    // from information for LaTeX output (None for root)
    from: Option<usize>,
    // number of children nodes
    children_cnt: usize,
    // formula id
    id: usize,
    // sided formula
    fml: SidedFormula<'a>,
}

impl<'a> ProofNode<'a> {
    /// Create new root proof node with None as from value
    #[inline(always)]
    fn new_root(
        seq: Sequent<'a>,
        formula_map: FxHashMap<usize, SidedFormula<'a>>,
        added_formulas: Vec<(usize, SidedFormula<'a>)>,
    ) -> Self {
        Self {
            seq,
            children_cnt: OnceCell::new(),
            proved_children_cnt: 0,
            parent_idx: None,
            formula_map,
            added_formulas,
            from: None,
        }
    }

    /// Create new child proof node with from_formula's id as from value
    #[inline(always)]
    fn new(
        seq: Sequent<'a>,
        formula_map: FxHashMap<usize, SidedFormula<'a>>,
        added_formulas: Vec<(usize, SidedFormula<'a>)>,
        parent_idx: usize,
        from_formula: SidedFormula<'a>,
    ) -> Self {
        // use get_from for non-root nodes
        let from = Some(from_formula.get_from(&formula_map));
        Self {
            seq,
            children_cnt: OnceCell::new(),
            proved_children_cnt: 0,
            parent_idx: Some(parent_idx),
            formula_map,
            added_formulas,
            from,
        }
    }
}

impl<'a> ForestNode<'a> {
    /// Create new forest node for LaTeX output
    fn new(from: Option<usize>, children_cnt: usize, id: usize, fml: SidedFormula<'a>) -> Self {
        Self {
            from,
            children_cnt,
            id,
            fml,
        }
    }
}

impl<'a> SidedFormula<'a> {
    /// Get id of sided formula from formula map for generating from information
    #[inline(always)]
    fn get_from(&self, formula_map: &FxHashMap<usize, SidedFormula<'a>>) -> usize {
        formula_map
            .iter()
            .find_map(|(id, p)| if p == self { Some(*id) } else { None })
            .unwrap()
    }

    /// Convert sided formula to tableau representation for display
    fn to_tablau(&self) -> Formula {
        let fml = self.fml.clone();
        match self.side {
            Left => fml,
            Right => Not(Box::new(fml)),
        }
    }
}

/// Generates a LaTeX proof tree using the forest package.
pub fn forest(seq: Sequent, names: &Names, out: &str) -> io::Result<()> {
    // buffer for storing the proof tree string
    let mut buf: Vec<u8> = Vec::with_capacity(MAX_FILE_SIZE);
    let mut forest_nodes: Vec<ForestNode> = Vec::new();
    // generate the proof tree
    forest_impl(seq.clone(), &mut forest_nodes)?;
    // reorder forest nodes using stack-based algorithm
    let forest_nodes = reorder_forest_nodes(forest_nodes);
    // Write the proof tree content
    write_forest_latex(&forest_nodes, names, &mut buf)?;
    // create output LaTeX file
    let mut file = File::create(PathBuf::from(out).join("forest.tex"))?;
    // replace the placeholder with proof
    let proof = include_str!("../../templates/forest.tex")
        .replace(
            "%CLAIM%",
            &seq.display(names)
                .to_string()
                .replace(r"&\vdash", r"\vdash")
                .trim(),
        )
        .replace("%PROOF_CONTENT%", &String::from_utf8_lossy(&buf).trim());
    // write proof
    file.write_all(proof.as_bytes())?;
    Ok(())
}

/// Implementation for generating LaTeX proof trees.
fn forest_impl<'a>(seq: Sequent<'a>, forest_nodes: &mut Vec<ForestNode<'a>>) -> io::Result<()> {
    // global unique id counter for formulas
    let mut global_id = 1;
    // create initial formula map with id assignment
    let mut formula_map = FxHashMap::default();
    let mut added_formulas = Vec::new();

    for p in seq.iter() {
        formula_map.insert(global_id, *p);
        added_formulas.push((global_id, *p));
        global_id += 1;
    }

    if seq.is_initially_trivial() {
        // trivial from the beginning
        // ex. p, q ⊢ r, p
        // create individual forest nodes for each formula
        for (i, (id, fml)) in added_formulas.iter().enumerate() {
            let children_cnt = if i == added_formulas.len() - 1 { 0 } else { 1 };
            let forest_node = ForestNode::new(None, children_cnt, *id, *fml);
            forest_nodes.push(forest_node);
        }
        return Ok(());
    }

    let mut nodes = vec![ProofNode::new_root(seq, formula_map, added_formulas)];

    'main: loop {
        // write all proved nodes to forest_nodes
        flush_proved_nodes(&mut nodes, forest_nodes)?;
        // get the last sequent for processing
        let Some(ProofNode { children_cnt, .. }) = nodes.last() else {
            // if no sequent to be proved, completed the proof
            return Ok(());
        };
        let ProofNode {
            mut seq,
            mut formula_map,
            ..
        } = nodes.last().unwrap().clone();
        // get the last formula for decomposition
        let fml = seq.pop().unwrap();
        let from_formula = fml;
        let SidedFormula { fml, side } = fml;

        match (fml, side) {
            // convert `¬p ⊢` to `⊢ p`
            // convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                children_cnt.set(1).unwrap();
                let p = p.with_side(side.opposite());
                formula_map.insert(global_id, p);
                let added_formulas = vec![(global_id, p)];
                global_id += 1;
                let is_trivial = seq.is_trivial(p);

                seq.push(p);
                let seq = ProofNode::new(
                    seq,
                    formula_map,
                    added_formulas,
                    nodes.len() - 1,
                    from_formula,
                );
                if is_trivial {
                    seq.children_cnt.set(0).unwrap();
                }
                nodes.push(seq);
            }
            // convert `p ∧ q ∧ r ⊢` to `p, q, r ⊢`
            // convert `⊢ p ∨ q ∨ r` to `⊢ p, q, r`
            (And(l), Left) | (Or(l), Right) => {
                children_cnt.set(1).unwrap();
                let mut is_trivial = false;
                let mut added_formulas = Vec::new();
                for p in l {
                    let p = p.with_side(side);
                    formula_map.insert(global_id, p);
                    added_formulas.push((global_id, p));
                    global_id += 1;
                    if seq.is_trivial(p) {
                        is_trivial = true;
                    }
                    seq.push(p);
                }
                let seq = ProofNode::new(
                    seq,
                    formula_map,
                    added_formulas,
                    nodes.len() - 1,
                    from_formula,
                );
                if is_trivial {
                    seq.children_cnt.set(0).unwrap();
                }
                nodes.push(seq);
            }
            // convert `p ∨ q ∨ r ⊢` to `p ⊢` and `q ⊢` and `r ⊢`
            // convert `⊢ p ∧ q ∧ r` to `⊢ p` and `⊢ q` and `⊢ r`
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
                children_cnt.set(l.len()).unwrap();
                let parent_idx = nodes.len() - 1;
                global_id += l.len();
                for p in l.iter().rev() {
                    let mut formula_map = formula_map.clone();
                    let p = p.with_side(side);
                    global_id -= 1;
                    formula_map.insert(global_id, p);
                    let added_formulas = vec![(global_id, p)];
                    let is_trivial = seq.is_trivial(p);

                    let mut seq = seq.clone();
                    seq.push(p);
                    let seq_node = ProofNode::new(
                        seq,
                        formula_map.clone(),
                        added_formulas,
                        parent_idx,
                        from_formula,
                    );
                    if is_trivial {
                        seq_node.children_cnt.set(0).unwrap();
                    }
                    nodes.push(seq_node);
                }
                global_id += l.len();
            }
            // convert `p → q ⊢` to `⊢ p` and `q ⊢`
            (To(p, q), Left) => {
                let q = q.with_side(Left);
                if q.is_atom() && seq.contains_atom(&q) {
                    // when `fml` is redundant
                    // ex. `p → q, q ⊢`
                    // drop `fml` and continue to the next sequent
                    nodes.last_mut().unwrap().seq.pop();
                    continue 'main;
                }
                children_cnt.set(2).unwrap();
                let p = p.with_side(Right);
                let mut formula_map1 = formula_map.clone();
                let mut formula_map2 = formula_map;
                formula_map1.insert(global_id + 1, q);
                let added_formulas1 = vec![(global_id + 1, q)];
                formula_map2.insert(global_id, p);
                let added_formulas2 = vec![(global_id, p)];
                global_id += 2;
                let is_trivial_q = seq.is_trivial(q);
                let is_trivial_p = seq.is_trivial(p);

                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(q);
                seq2.push(p);
                let parent_idx = nodes.len() - 1;
                let seq1 = ProofNode::new(
                    seq1,
                    formula_map1,
                    added_formulas1,
                    parent_idx,
                    from_formula,
                );
                let seq2 = ProofNode::new(
                    seq2,
                    formula_map2,
                    added_formulas2,
                    parent_idx,
                    from_formula,
                );

                if is_trivial_q {
                    seq1.children_cnt.set(0).unwrap();
                }
                if is_trivial_p {
                    seq2.children_cnt.set(0).unwrap();
                }
                nodes.push(seq1);
                nodes.push(seq2);
            }
            // convert `⊢ p → q` to `p ⊢ q`
            (To(p, q), Right) => {
                children_cnt.set(1).unwrap();
                let p = p.with_side(Left);
                let q = q.with_side(Right);
                formula_map.insert(global_id, p);
                global_id += 1;
                formula_map.insert(global_id, q);
                global_id += 1;
                let added_formulas = vec![(global_id - 2, p), (global_id - 1, q)];
                let is_trivial = seq.is_trivial2(p, q);

                seq.push(p);
                seq.push(q);
                let seq = ProofNode::new(
                    seq,
                    formula_map,
                    added_formulas,
                    nodes.len() - 1,
                    from_formula,
                );
                if is_trivial {
                    seq.children_cnt.set(0).unwrap();
                }
                nodes.push(seq);
            }
            // convert `p ↔ q ⊢` to `p, q ⊢` and `⊢ p, q`
            // convert `⊢ p ↔ q` to `p ⊢ q` and `q ⊢ p`
            (Iff(p, q), side) => {
                children_cnt.set(2).unwrap();
                let p_l = p.with_side(Left);
                let p_r = p.with_side(Right);
                let q_l = q.with_side(Left);
                let q_r = q.with_side(Right);
                let (fml11, fml12, fml21, fml22) = match side {
                    Left => (p_r, q_r, p_l, q_l),
                    Right => (q_l, p_r, p_l, q_r),
                };
                let mut formula_map1 = formula_map.clone();
                let mut formula_map2 = formula_map;
                formula_map1.insert(global_id + 2, fml11);
                formula_map1.insert(global_id + 3, fml12);
                let added_formulas1 = vec![(global_id + 2, fml11), (global_id + 3, fml12)];
                formula_map2.insert(global_id, fml21);
                formula_map2.insert(global_id + 1, fml22);
                let added_formulas2 = vec![(global_id, fml21), (global_id + 1, fml22)];
                global_id += 4;
                let is_trivial_1 = seq.is_trivial2(fml11, fml12);
                let is_trivial_2 = seq.is_trivial2(fml21, fml22);

                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(fml11);
                seq1.push(fml12);
                seq2.push(fml21);
                seq2.push(fml22);
                let parent_idx = nodes.len() - 1;
                let seq1 = ProofNode::new(
                    seq1,
                    formula_map1,
                    added_formulas1,
                    parent_idx,
                    from_formula,
                );
                let seq2 = ProofNode::new(
                    seq2,
                    formula_map2,
                    added_formulas2,
                    parent_idx,
                    from_formula,
                );
                if is_trivial_1 {
                    seq1.children_cnt.set(0).unwrap();
                }
                if is_trivial_2 {
                    seq2.children_cnt.set(0).unwrap();
                }
                nodes.push(seq1);
                nodes.push(seq2);
            }
            (Pred(..), _) => {
                // since formulas in 'seq' are ordered,
                // if `fml` is predicate, no formulas can be processed
                // thus, it is impossible to prove
                unreachable!()
            }
            (Ex(..) | All(..), _) => unimplemented!(),
        }
    }
}

/// Writes all proved nodes to the LaTeX buffer.
/// - Processes only when all their children are proved
/// - Automatically increments parent nodes' count of proved children
fn flush_proved_nodes<'a>(
    nodes: &mut Vec<ProofNode<'a>>,
    forest_nodes: &mut Vec<ForestNode<'a>>,
) -> io::Result<()> {
    while let Some(node) = nodes.last() {
        let Some(children_cnt_val) = node.children_cnt.get() else {
            // not processed yet
            break;
        };
        if node.proved_children_cnt < *children_cnt_val {
            // if has unproved children, stop processing
            break;
        }
        let children_cnt_val = *children_cnt_val;

        // get parent_idx before removing the node
        let parent_idx = node.parent_idx;

        if let Some(parent_idx) = parent_idx {
            // if has a parent
            // increment the parent's proved children count
            nodes[parent_idx].proved_children_cnt += 1;
        }

        // remove the completed node and use it directly
        let mut completed_node = nodes.pop().unwrap();

        // first formula gets the actual children_cnt
        let (id, fml) = completed_node.added_formulas.pop().unwrap();
        let first_forest_node = ForestNode::new(completed_node.from, children_cnt_val, id, fml);
        forest_nodes.push(first_forest_node);

        // remaining formulas get children_cnt = 1
        while let Some((id, fml)) = completed_node.added_formulas.pop() {
            let forest_node = ForestNode::new(completed_node.from, 1, id, fml);
            forest_nodes.push(forest_node);
        }
    }
    Ok(())
}

fn check_buf_size(buf: &Vec<u8>) {
    if buf.len() > MAX_FILE_SIZE {
        // terminate the entire process immediately
        error!("Failed: File size exceeded the limit.");
        panic!("File size exceeded the limit.");
    }
}

/// Reorder forest nodes using stack-based algorithm similar to reverse Polish notation
/// - Pop nodes from input vector in reverse order
/// - Pop children_cnt elements from stack and combine with current node
/// - Children are inserted in reverse order of popping to maintain correct structure
fn reorder_forest_nodes<'a>(mut forest_nodes: Vec<ForestNode<'a>>) -> Vec<ForestNode<'a>> {
    // stack of node vectors for processing
    let mut stack: Vec<Vec<ForestNode<'a>>> = Vec::new();

    forest_nodes.reverse();

    // process nodes in reverse order (pop from end)
    while let Some(node) = forest_nodes.pop() {
        let children_cnt = node.children_cnt;

        // start with current node
        let mut combined = vec![node];

        // collect children in temporary buffer to reverse pop order
        let mut children = Vec::with_capacity(children_cnt);
        for _ in 0..children_cnt {
            let child_vec = stack.pop().unwrap();
            children.push(child_vec);
        }

        // extend in reverse order of popping (but keep internal order of each child_vec)
        for child_vec in children.into_iter().rev() {
            // clone to get ForestNode, not &ForestNode
            combined.extend(child_vec);
        }

        stack.push(combined);
    }

    // stack should contain exactly one element at the end
    assert!(stack.len() == 1);

    stack.into_iter().next().unwrap()
}

/// Write forest nodes to LaTeX buffer using stack-based algorithm
/// - Stack tracks remaining children count for each node
/// - Indent management for proper LaTeX formatting
/// - Automatic closing of brackets when children count reaches zero
fn write_forest_latex<'a>(
    forest_nodes: &[ForestNode<'a>],
    names: &Names,
    buf: &mut Vec<u8>,
) -> io::Result<()> {
    // stack of remaining children count
    let mut stack = vec![];
    // current indentation level
    let mut ind = 0;

    for ForestNode {
        from,
        children_cnt,
        id,
        fml,
    } in forest_nodes
    {
        // let from = from.map_or("".to_string(), |i| i.to_string());
        let from = from.map_or(String::new(), |i| format!(",from={}", i));

        if *children_cnt != 0 {
            // internal node - write opening bracket
            check_buf_size(buf);
            writeln!(
                buf,
                "{:ind$}[{},idx={}{}",
                "",
                fml.to_tablau().display(names),
                id,
                from,
                ind = ind * 2
            )?;

            // increment indentation for children
            ind += 1;
            // push current node's children count to stack
            stack.push(*children_cnt);
            continue;
        }

        // leaf node - write with close attribute
        check_buf_size(buf);
        writeln!(
            buf,
            "{:ind$}[{},idx={}{},close]",
            "",
            fml.to_tablau().display(names),
            id,
            from,
            ind = ind * 2
        )?;

        // decrement children count of parent on stack
        *stack.last_mut().unwrap() -= 1;

        // process completed nodes on stack
        while let Some(&children_cnt) = stack.last() {
            if children_cnt == 0 {
                // node completed - pop from stack and close bracket
                stack.pop();
                ind -= 1;
                check_buf_size(buf);
                writeln!(buf, "{:ind$}]", "", ind = ind * 2)?;

                // decrement parent's children count if exists
                if let Some(parent_children) = stack.last_mut() {
                    *parent_children -= 1;
                }
            } else {
                // node still has remaining children
                break;
            }
        }
    }

    // stack should be empty at the end
    assert!(stack.is_empty());
    Ok(())
}
