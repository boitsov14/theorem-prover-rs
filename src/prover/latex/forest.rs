use crate::{
    core::{
        names::Names,
        syntax::Formula::{self, *},
    },
    prover::sequent::{
        Sequent,
        Side::{Left, Right},
        SidedFormula,
    },
};
use log::error;
use rustc_hash::FxHashMap;
use std::{cell::OnceCell, fs::File, io::Write, path::PathBuf, vec};

const MAX_FILE_SIZE: usize = 1_000_000; // 1MB

#[derive(Clone, Debug)]
struct ProofNode<'a> {
    seq: Sequent<'a>,
    children_cnt: OnceCell<usize>,
    proved_children_cnt: usize,
    /// None if root
    parent_idx: Option<usize>,
    /// Maps formula to its tableau node id
    fml_to_id: FxHashMap<SidedFormula<'a>, usize>,
    local_tableau_nodes: Vec<PartialTableauNode<'a>>,
}

/// Intermediate tableau node during proof construction phase
#[derive(Clone, Debug)]
struct PartialTableauNode<'a> {
    id: usize,
    fml: SidedFormula<'a>,
    /// Source tableau node id that this formula was logically derived from (0 for root)
    from_id: usize,
}

/// For LaTeX generation output
#[derive(Clone, Debug)]
struct TableauNode<'a> {
    id: usize,
    fml: SidedFormula<'a>,
    /// Source tableau node id that this formula was logically derived from (0 for root)
    from_id: usize,
    children_cnt: usize,
}

impl<'a> ProofNode<'a> {
    #[inline(always)]
    const fn new_root(
        seq: Sequent<'a>,
        fml_to_id: FxHashMap<SidedFormula<'a>, usize>,
        local_tableau_nodes: Vec<PartialTableauNode<'a>>,
    ) -> Self {
        Self {
            seq,
            children_cnt: OnceCell::new(),
            proved_children_cnt: 0,
            parent_idx: None,
            fml_to_id,
            local_tableau_nodes,
        }
    }

    #[inline(always)]
    const fn new(
        seq: Sequent<'a>,
        parent_idx: usize,
        fml_to_id: FxHashMap<SidedFormula<'a>, usize>,
        local_tableau_nodes: Vec<PartialTableauNode<'a>>,
    ) -> Self {
        Self {
            seq,
            children_cnt: OnceCell::new(),
            proved_children_cnt: 0,
            parent_idx: Some(parent_idx),
            fml_to_id,
            local_tableau_nodes,
        }
    }
}

impl<'a> PartialTableauNode<'a> {
    const fn new(id: usize, fml: SidedFormula<'a>, from_id: usize) -> Self {
        Self { id, fml, from_id }
    }

    /// Convert `PartialTableauNode` to `TableauNode` with children count.
    const fn to_tableau_node(&self, children_cnt: usize) -> TableauNode<'a> {
        TableauNode::new(self.id, self.fml, self.from_id, children_cnt)
    }
}

impl<'a> TableauNode<'a> {
    const fn new(id: usize, fml: SidedFormula<'a>, from_id: usize, children_cnt: usize) -> Self {
        Self {
            id,
            fml,
            from_id,
            children_cnt,
        }
    }
}

impl SidedFormula<'_> {
    /// Convert formula to tableau representation for display.
    fn to_tableau_form(self) -> Formula {
        let fml = self.fml.clone();
        match self.side {
            Left => fml,
            Right => Not(Box::new(fml)),
        }
    }
}

/// Generates a LaTeX proof tree using the forest package.
pub fn forest(seq: Sequent, names: &Names, out: &str) {
    let claim = seq
        .display(names)
        .to_string()
        .replace(r"&\vdash", r"\vdash")
        .replace(',', r"{,}\,");
    // buffer for storing the proof tree string
    let mut buf = Vec::with_capacity(MAX_FILE_SIZE);
    // generate the proof tree
    let nodes = forest_impl(seq);
    // reorder forest nodes using stack-based algorithm
    let nodes = mirror_tree(nodes);
    // Write the proof tree content
    write_latex(&nodes, names, &mut buf);
    // create output LaTeX file
    let mut file = File::create(PathBuf::from(out).join("forest.tex")).unwrap();
    // replace the placeholder with proof
    let proof = include_str!("../../../templates/forest.tex")
        .replace("%CLAIM%", claim.trim())
        .replace("%PROOF_CONTENT%", String::from_utf8_lossy(&buf).trim());
    // write proof
    file.write_all(proof.as_bytes()).unwrap();
}

/// Implementation for generating LaTeX proof trees.
///
/// `ProofNode`:
/// ```text
///      1            1            1            1            1            1
///                  / \          / \          / \          / \          / \
///                 2   3        2   3        2   3        2   3        2   3
///                             / \          / \          / \ / \      / \ / \
///                            4   5        4   5        4  5 6  7    4  5 6  7
/// ```
/// `nodes`:
/// ```text
///                               [4]
///                               [5]                       [6]
///                  [2]          [2]                       [7]
///                  [3]          [3]          [3]          [3]
///     [1]          [1]          [1]          [1]          [1]          ___
/// ```
/// `tableau_nodes`:
/// ```text
///                                                                      [1]
///                                                                      [3]
///                                                                      [7]
///                                                                      [6]
///                                            [2]          [2]          [2]
///                                            [5]          [5]          [5]
///     ___          ___          ___          [4]          [4]          [4]
/// ```
fn forest_impl(seq: Sequent<'_>) -> Vec<TableauNode<'_>> {
    // global unique id counter for tableau node id
    let mut id = 1;
    // formula-to-id mapping
    let mut fml_to_id = FxHashMap::default();
    let mut local_tableau_nodes = vec![];
    let mut tableau_nodes = vec![];

    // check if the sequent is initially trivial
    let is_initially_trivial = seq.is_initially_trivial();

    // setup initial local tableau nodes
    for p in seq.iter() {
        fml_to_id.insert(*p, id);
        local_tableau_nodes.push(PartialTableauNode::new(id, *p, 0));
        id += 1;
    }

    let root = ProofNode::new_root(seq, fml_to_id, local_tableau_nodes);

    if is_initially_trivial {
        // trivial from the beginning
        // ex. p, q ⊢ r, p
        // set children_cnt to 0
        root.children_cnt.set(0).unwrap();
    }

    let mut nodes = vec![root];

    'main: loop {
        // flushes proved nodes to tableau nodes
        flush_proved_nodes(&mut nodes, &mut tableau_nodes);
        // get the last sequent
        let Some(ProofNode {
            seq,
            fml_to_id,
            children_cnt,
            ..
        }) = nodes.last()
        else {
            // if no sequent to be proved, completed the proof
            return tableau_nodes;
        };
        // clone for new proof node
        let mut seq = seq.clone();
        let mut fml_to_id = fml_to_id.clone();
        // get the last formula
        // safe unwrap: provable sequents contain processable formulas
        let fml = seq.pop().unwrap();
        // get the from_id
        let from_id = fml_to_id[&fml];
        let SidedFormula { fml, side } = fml;
        match (fml, side) {
            // convert `¬p ⊢` to `⊢ p`
            // convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                // set children_cnt to 1
                children_cnt.set(1).unwrap();
                let p = p.with_side(side.opposite());
                let is_trivial = seq.is_trivial(p);
                seq.push(p);
                // setup formula-to-id mapping
                fml_to_id.insert(p, id);
                let local_tableau_nodes = vec![PartialTableauNode::new(id, p, from_id)];
                id += 1;
                let parent_idx = nodes.len() - 1;
                let node = ProofNode::new(seq, parent_idx, fml_to_id, local_tableau_nodes);
                if is_trivial {
                    // if trivial, set children_cnt to 0
                    node.children_cnt.set(0).unwrap();
                }
                nodes.push(node);
            }
            // convert `p ∧ q ∧ r ⊢` to `p, q, r ⊢`
            // convert `⊢ p ∨ q ∨ r` to `⊢ p, q, r`
            // Drop `true` or `false` in `true ⊢` or `⊢ false`
            (And(l), Left) | (Or(l), Right) => {
                if l.is_empty() {
                    // `true ⊢` and `⊢ false`
                    // avoid showing trivial true/false elimination step
                    // drop `fml` and continue to the next sequent
                    nodes.last_mut().unwrap().seq.pop();
                    continue 'main;
                }
                // set children_cnt to 1
                children_cnt.set(1).unwrap();
                let mut is_trivial = false;
                let mut local_tableau_nodes = vec![];
                for p in l {
                    let p = p.with_side(side);
                    // setup formula-to-id mapping
                    fml_to_id.insert(p, id);
                    let local_tableau_node = PartialTableauNode::new(id, p, from_id);
                    local_tableau_nodes.push(local_tableau_node);
                    id += 1;
                    if seq.is_trivial(p) {
                        is_trivial = true;
                    }
                    seq.push(p);
                }
                let parent_idx = nodes.len() - 1;
                let node = ProofNode::new(seq, parent_idx, fml_to_id, local_tableau_nodes);
                if is_trivial {
                    // if trivial, set children_cnt to 0
                    node.children_cnt.set(0).unwrap();
                }
                nodes.push(node);
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
                // set children count
                children_cnt.set(l.len()).unwrap();
                let parent_idx = nodes.len() - 1;
                // temp nodes
                let mut temp_nodes = Vec::with_capacity(l.len());
                for p in l {
                    let p = p.with_side(side);
                    // setup formula-to-id mapping
                    let mut fml_to_id = fml_to_id.clone();
                    fml_to_id.insert(p, id);
                    let local_tableau_nodes = vec![PartialTableauNode::new(id, p, from_id)];
                    id += 1;
                    let is_trivial = seq.is_trivial(p);
                    let mut seq = seq.clone();
                    seq.push(p);
                    let node = ProofNode::new(seq, parent_idx, fml_to_id, local_tableau_nodes);
                    if is_trivial {
                        // if trivial, set children_cnt to 0
                        node.children_cnt.set(0).unwrap();
                    }
                    temp_nodes.push(node);
                }
                nodes.extend(temp_nodes.into_iter().rev());
            }
            // convert `p → q ⊢` to `⊢ p` and `q ⊢`
            (To(p, q), Left) => {
                let q = q.with_side(Left);
                // check if `fml` is redundant
                if q.is_atom() && seq.contains_atom(&q) {
                    // ex. `p → q, q ⊢`
                    // drop this `fml` and continue to the next sequent
                    nodes.last_mut().unwrap().seq.pop();
                    continue 'main;
                }
                // set children count to 2
                children_cnt.set(2).unwrap();
                let p = p.with_side(Right);
                // setup each formula-to-id mappings
                let mut fml_to_id1 = fml_to_id.clone();
                let mut fml_to_id2 = fml_to_id;
                fml_to_id1.insert(p, id);
                let local_tableau_nodes1 = vec![PartialTableauNode::new(id, p, from_id)];
                id += 1;
                fml_to_id2.insert(q, id);
                let local_tableau_nodes2 = vec![PartialTableauNode::new(id, q, from_id)];
                id += 1;
                let is_trivial_p = seq.is_trivial(p);
                let is_trivial_q = seq.is_trivial(q);
                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(p);
                seq2.push(q);
                let parent_idx = nodes.len() - 1;
                let node1 = ProofNode::new(seq1, parent_idx, fml_to_id1, local_tableau_nodes1);
                let node2 = ProofNode::new(seq2, parent_idx, fml_to_id2, local_tableau_nodes2);
                if is_trivial_p {
                    // if trivial, set children count to 0
                    node1.children_cnt.set(0).unwrap();
                }
                if is_trivial_q {
                    // if trivial, set children count to 0
                    node2.children_cnt.set(0).unwrap();
                }
                // we need to process `node1` first, so push `node1` later
                nodes.push(node2);
                nodes.push(node1);
            }
            // convert `⊢ p → q` to `p ⊢ q`
            (To(p, q), Right) => {
                // set children count to 1
                children_cnt.set(1).unwrap();
                let p = p.with_side(Left);
                let q = q.with_side(Right);
                // setup formula-to-id mappings
                fml_to_id.insert(p, id);
                let local_tableau_node1 = PartialTableauNode::new(id, p, from_id);
                id += 1;
                fml_to_id.insert(q, id);
                let local_tableau_node2 = PartialTableauNode::new(id, q, from_id);
                id += 1;
                // setup local tableau nodes
                let local_tableau_nodes = vec![local_tableau_node1, local_tableau_node2];
                let is_trivial = seq.is_trivial2(p, q);
                seq.push(p);
                seq.push(q);
                let parent_idx = nodes.len() - 1;
                let node = ProofNode::new(seq, parent_idx, fml_to_id, local_tableau_nodes);
                if is_trivial {
                    // if trivial, set children count to 0
                    node.children_cnt.set(0).unwrap();
                }
                nodes.push(node);
            }
            // convert `p ↔ q ⊢` to `p, q ⊢` and `⊢ p, q`
            // convert `⊢ p ↔ q` to `p ⊢ q` and `q ⊢ p`
            (Iff(p, q), side) => {
                // set children count to 2
                children_cnt.set(2).unwrap();
                let p_l = p.with_side(Left);
                let p_r = p.with_side(Right);
                let q_l = q.with_side(Left);
                let q_r = q.with_side(Right);
                let (fml11, fml12, fml21, fml22) = match side {
                    Left => (p_l, q_l, p_r, q_r),
                    Right => (p_l, q_r, q_l, p_r),
                };
                // setup formula-to-id mappings
                let mut fml_to_id1 = fml_to_id.clone();
                let mut fml_to_id2 = fml_to_id;
                fml_to_id1.insert(fml11, id);
                let local_tableau_node11 = PartialTableauNode::new(id, fml11, from_id);
                id += 1;
                fml_to_id1.insert(fml12, id);
                let local_tableau_node12 = PartialTableauNode::new(id, fml12, from_id);
                id += 1;
                let local_tableau_nodes1 = vec![local_tableau_node11, local_tableau_node12];
                fml_to_id2.insert(fml21, id);
                let local_tableau_node21 = PartialTableauNode::new(id, fml21, from_id);
                id += 1;
                fml_to_id2.insert(fml22, id);
                let local_tableau_node22 = PartialTableauNode::new(id, fml22, from_id);
                id += 1;
                let local_tableau_nodes2 = vec![local_tableau_node21, local_tableau_node22];
                let is_trivial1 = seq.is_trivial2(fml11, fml12);
                let is_trivial2 = seq.is_trivial2(fml21, fml22);
                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(fml11);
                seq1.push(fml12);
                seq2.push(fml21);
                seq2.push(fml22);
                let parent_idx = nodes.len() - 1;
                let node1 = ProofNode::new(seq1, parent_idx, fml_to_id1, local_tableau_nodes1);
                let node2 = ProofNode::new(seq2, parent_idx, fml_to_id2, local_tableau_nodes2);
                if is_trivial1 {
                    // if trivial, set children count to 0
                    node1.children_cnt.set(0).unwrap();
                }
                if is_trivial2 {
                    // if trivial, set children count to 0
                    node2.children_cnt.set(0).unwrap();
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

/// Flushes proved nodes to tableau nodes.
///
/// `ProofNode`:
/// ```text
///     1
///    / \
///   2   3
///  / \ / \
/// 4  5 6  7
/// ```
/// `nodes`:
/// ```text
///    [4]
/// [5-1,2,3]  [5-1,2,3]
///  [2-1,2]    [2-1,2]    [2-1,2]
///    [3]        [3]        [3]        [3]
///    [1]        [1]        [1]        [1]
/// ```
/// `tableau_nodes`:
/// ```text
///                                    [2-1]
///                                    [2-2]
///                         [5-1]      [5-1]
///                         [5-2]      [5-2]
///                         [5-3]      [5-3]
///     ___       [4]        [4]        [4]
/// ```
fn flush_proved_nodes<'a>(
    nodes: &mut Vec<ProofNode<'a>>,
    tableau_nodes: &mut Vec<TableauNode<'a>>,
) {
    while let Some(node) = nodes.last() {
        // check if the children count has been set
        let Some(children_cnt) = node.children_cnt.get() else {
            // not processed yet
            break;
        };
        assert_eq!(
            *children_cnt, node.proved_children_cnt,
            "all children should be proved"
        );
        let children_cnt = *children_cnt;

        if let Some(parent_idx) = node.parent_idx {
            // if has a parent
            // increment the parent's proved children count
            nodes[parent_idx].proved_children_cnt += 1;
        }

        let mut node = nodes.pop().unwrap();

        // convert local tableau nodes to tableau nodes
        let local_tableau_node = node.local_tableau_nodes.pop().unwrap();
        tableau_nodes.push(local_tableau_node.to_tableau_node(children_cnt));

        while let Some(local_tableau_node) = node.local_tableau_nodes.pop() {
            tableau_nodes.push(local_tableau_node.to_tableau_node(1));
        }
    }
}

/// check buffer size and panic if it exceeds `MAX_FILE_SIZE`
fn check_buf_size(buf: &[u8]) {
    if buf.len() > MAX_FILE_SIZE {
        // terminate the entire process immediately
        error!("Failed: File size exceeded the limit.");
        panic!("File size exceeded the limit.");
    }
}

/// Mirror tableau nodes using stack-based algorithm similar to reverse Polish notation
///
/// `ProofNode`:
/// ```text
///     1
///    / \
///   2   3
///  / \ / \
/// 4  5 6  7
///
/// input:
/// [4, 5, 2, 6, 7, 3, 1]
///
/// processing:
/// stack: []
/// stack: [[4]]
/// stack: [[4], [5]]
/// stack: [[2, 4, 5]]
/// stack: [[2, 4, 5], [6]]
/// stack: [[2, 4, 5], [6], [7]]
/// stack: [[2, 4, 5], [3, 6, 7]]
/// stack: [[1, 2, 4, 5, 3, 6, 7]]
///
/// result:
/// [1, 2, 4, 5, 3, 6, 7]
/// ```
fn mirror_tree(nodes: Vec<TableauNode<'_>>) -> Vec<TableauNode<'_>> {
    // stack of node vectors
    // each vector represents a subtree
    let mut stack = vec![];

    for node in nodes {
        let children_cnt = node.children_cnt;

        // create new subtree starting with current node as root
        let mut new_vec = vec![node];

        // drain last children count subtrees from stack and combine with current node
        for vec in stack.drain(stack.len() - children_cnt..) {
            new_vec.extend(vec);
        }

        // push the new combined subtree back to stack
        stack.push(new_vec);
    }

    assert_eq!(stack.len(), 1, "stack should contain exactly one subtree");

    stack.pop().unwrap()
}

/// Write tableau nodes to LaTeX buffer using stack-based algorithm
fn write_latex(tableau_nodes: &[TableauNode<'_>], names: &Names, buf: &mut Vec<u8>) {
    // stack of remaining children count of each parent node
    let mut stack = vec![];
    // current indentation
    let mut ind = 1;

    for TableauNode {
        id,
        fml,
        from_id,
        children_cnt,
    } in tableau_nodes
    {
        check_buf_size(buf);
        if *children_cnt != 0 {
            // internal node - write opening bracket
            if *from_id == 0 {
                // root node
                writeln!(
                    buf,
                    "{:ind$}[{},idx={id}",
                    "",
                    fml.to_tableau_form().display(names),
                    ind = ind * 2
                )
                .unwrap();
            } else {
                // child node
                writeln!(
                    buf,
                    "{:ind$}[{},idx={id},from={from_id}",
                    "",
                    fml.to_tableau_form().display(names),
                    ind = ind * 2
                )
                .unwrap();
            }

            // increment indentation
            ind += 1;
            // push current node's children count to stack
            stack.push(*children_cnt);
            continue;
        }

        // leaf node - write with close attribute
        if *from_id == 0 {
            // root node
            writeln!(
                buf,
                "{:ind$}[{},idx={id},close]",
                "",
                fml.to_tableau_form().display(names),
                ind = ind * 2
            )
            .unwrap();
        } else {
            // child node
            writeln!(
                buf,
                "{:ind$}[{},idx={id},from={from_id},close]",
                "",
                fml.to_tableau_form().display(names),
                ind = ind * 2
            )
            .unwrap();
        }

        // process completed nodes on stack
        while let Some(children_cnt) = stack.last_mut() {
            // decrement parent's children count
            *children_cnt -= 1;
            if *children_cnt != 0 {
                // parent still has remaining children
                break;
            }
            // all children processed
            // pop parent from stack and close bracket
            stack.pop();
            ind -= 1;
            writeln!(buf, "{:ind$}]", "", ind = ind * 2).unwrap();
        }
    }

    assert!(stack.is_empty(), "stack should be empty at the end");
}
