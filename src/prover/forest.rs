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
use std::{cell::OnceCell, fs::File, io::Write, path::PathBuf, vec};

const MAX_FILE_SIZE: usize = 1_000_000; // 1MB

#[derive(Clone, Debug)]
struct ProofNode<'a> {
    seq: Sequent<'a>,
    children_cnt: OnceCell<usize>,
    proved_children_cnt: usize,
    /// None if root
    parent_idx: Option<usize>,
    /// Maps formula to its unique tableau node id
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
    fn new_root(
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
    fn new(
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
    fn new(id: usize, fml: SidedFormula<'a>, from_id: usize) -> Self {
        Self { id, fml, from_id }
    }

    /// Convert `PartialTableauNode` to `TableauNode` with children count.
    fn to_tableau_node(&self, children_cnt: usize) -> TableauNode<'a> {
        TableauNode::new(self.id, self.fml, self.from_id, children_cnt)
    }
}

impl<'a> TableauNode<'a> {
    fn new(id: usize, fml: SidedFormula<'a>, from_id: usize, children_cnt: usize) -> Self {
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
    let claim = &seq
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
    let proof = include_str!("../../templates/forest.tex")
        .replace("%CLAIM%", claim)
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
/// `new_nodes`:
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
    let mut fml_to_id = FxHashMap::default();
    let mut local_tableau_nodes = Vec::new();
    let mut new_nodes = vec![];

    for p in seq.iter() {
        fml_to_id.insert(*p, id);
        local_tableau_nodes.push(PartialTableauNode::new(id, *p, 0));
        id += 1;
    }

    if seq.is_initially_trivial() {
        // trivial from the beginning
        // ex. p, q ⊢ r, p
        // create individual forest nodes for each formula
        while let Some(node) = local_tableau_nodes.pop() {
            // if not empty, current node has one child, otherwise no children
            let children_cnt = usize::from(!local_tableau_nodes.is_empty());
            let node = node.to_tableau_node(children_cnt);
            new_nodes.push(node);
        }
        return new_nodes;
    }

    let mut nodes = vec![ProofNode::new_root(seq, fml_to_id, local_tableau_nodes)];

    'main: loop {
        // write all proved nodes to forest_nodes
        flush_proved_nodes(&mut nodes, &mut new_nodes);
        // get the last sequent
        let Some(ProofNode { seq, fml_to_id, .. }) = nodes.last() else {
            // if no sequent to be proved, completed the proof
            return new_nodes;
        };
        let mut seq = seq.clone();
        let mut fml_to_id = fml_to_id.clone();
        // get the last formula
        let fml = seq.pop().unwrap();
        let from_formula = fml;
        let SidedFormula { fml, side } = fml;

        match (fml, side) {
            // convert `¬p ⊢` to `⊢ p`
            // convert `⊢ ¬p` to `p ⊢`
            (Not(p), _) => {
                // set children_cnt for the last ProofNode
                nodes.last().unwrap().children_cnt.set(1).unwrap();
                let p = p.with_side(side.opposite());
                fml_to_id.insert(p, id);
                let from_id = fml_to_id[&from_formula];
                let local_tableau_nodes = vec![PartialTableauNode::new(id, p, from_id)];
                id += 1;
                let is_trivial = seq.is_trivial(p);

                seq.push(p);
                let new_node = ProofNode::new(seq, nodes.len() - 1, fml_to_id, local_tableau_nodes);
                if is_trivial {
                    // set children_cnt to 0 for trivial case
                    new_node.children_cnt.set(0).unwrap();
                }
                nodes.push(new_node);
            }
            // convert `p ∧ q ∧ r ⊢` to `p, q, r ⊢`
            // convert `⊢ p ∨ q ∨ r` to `⊢ p, q, r`
            (And(l), Left) | (Or(l), Right) => {
                nodes.last().unwrap().children_cnt.set(1).unwrap();
                let mut is_trivial = false;
                let from_id = fml_to_id[&from_formula];
                let mut local_tableau_nodes = Vec::new();
                for p in l {
                    let p = p.with_side(side);
                    fml_to_id.insert(p, id);
                    local_tableau_nodes.push(PartialTableauNode::new(id, p, from_id));
                    id += 1;
                    if seq.is_trivial(p) {
                        is_trivial = true;
                    }
                    seq.push(p);
                }
                local_tableau_nodes.reverse();
                let new_node = ProofNode::new(seq, nodes.len() - 1, fml_to_id, local_tableau_nodes);
                if is_trivial {
                    new_node.children_cnt.set(0).unwrap();
                }
                nodes.push(new_node);
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
                nodes.last().unwrap().children_cnt.set(l.len()).unwrap();
                let parent_idx = nodes.len() - 1;
                let from_id = fml_to_id[&from_formula];
                id += l.len();
                for p in l.iter().rev() {
                    let mut fml_to_id_clone = fml_to_id.clone();
                    let p = p.with_side(side);
                    id -= 1;
                    fml_to_id_clone.insert(p, id);
                    let local_tableau_nodes = vec![PartialTableauNode::new(id, p, from_id)];
                    let is_trivial = seq.is_trivial(p);

                    let mut seq = seq.clone();
                    seq.push(p);
                    let new_node = ProofNode::new(
                        seq,
                        parent_idx,
                        fml_to_id_clone.clone(),
                        local_tableau_nodes,
                    );
                    if is_trivial {
                        new_node.children_cnt.set(0).unwrap();
                    }
                    nodes.push(new_node);
                }
                id += l.len();
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
                nodes.last().unwrap().children_cnt.set(2).unwrap();
                let p = p.with_side(Right);
                let mut formula_map1 = fml_to_id.clone();
                let mut formula_map2 = fml_to_id;
                let from_id = formula_map1[&from_formula];
                formula_map1.insert(q, id + 1);
                let local_tableau_nodes1 = vec![PartialTableauNode::new(id + 1, q, from_id)];
                formula_map2.insert(p, id);
                let local_tableau_nodes2 = vec![PartialTableauNode::new(id, p, from_id)];
                id += 2;
                let is_trivial_q = seq.is_trivial(q);
                let is_trivial_p = seq.is_trivial(p);

                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(q);
                seq2.push(p);
                let parent_idx = nodes.len() - 1;
                let new_node1 =
                    ProofNode::new(seq1, parent_idx, formula_map1, local_tableau_nodes1);
                let new_node2 =
                    ProofNode::new(seq2, parent_idx, formula_map2, local_tableau_nodes2);

                if is_trivial_q {
                    new_node1.children_cnt.set(0).unwrap();
                }
                if is_trivial_p {
                    new_node2.children_cnt.set(0).unwrap();
                }
                nodes.push(new_node1);
                nodes.push(new_node2);
            }
            // convert `⊢ p → q` to `p ⊢ q`
            (To(p, q), Right) => {
                nodes.last().unwrap().children_cnt.set(1).unwrap();
                let p = p.with_side(Left);
                let q = q.with_side(Right);
                fml_to_id.insert(p, id);
                id += 1;
                fml_to_id.insert(q, id);
                id += 1;
                let from_id = fml_to_id[&from_formula];
                let local_tableau_nodes = vec![
                    PartialTableauNode::new(id - 2, p, from_id),
                    PartialTableauNode::new(id - 1, q, from_id),
                ];
                let is_trivial = seq.is_trivial2(p, q);

                seq.push(p);
                seq.push(q);
                let new_node = ProofNode::new(seq, nodes.len() - 1, fml_to_id, local_tableau_nodes);
                if is_trivial {
                    new_node.children_cnt.set(0).unwrap();
                }
                nodes.push(new_node);
            }
            // convert `p ↔ q ⊢` to `p, q ⊢` and `⊢ p, q`
            // convert `⊢ p ↔ q` to `p ⊢ q` and `q ⊢ p`
            (Iff(p, q), side) => {
                nodes.last().unwrap().children_cnt.set(2).unwrap();
                let p_l = p.with_side(Left);
                let p_r = p.with_side(Right);
                let q_l = q.with_side(Left);
                let q_r = q.with_side(Right);
                let (fml11, fml12, fml21, fml22) = match side {
                    Left => (p_r, q_r, p_l, q_l),
                    Right => (q_l, p_r, p_l, q_r),
                };
                let mut formula_map1 = fml_to_id.clone();
                let mut formula_map2 = fml_to_id;
                let from_id = formula_map1[&from_formula];
                formula_map1.insert(fml11, id + 2);
                formula_map1.insert(fml12, id + 3);
                let local_tableau_nodes1 = vec![
                    PartialTableauNode::new(id + 2, fml11, from_id),
                    PartialTableauNode::new(id + 3, fml12, from_id),
                ];
                formula_map2.insert(fml21, id);
                formula_map2.insert(fml22, id + 1);
                let local_tableau_nodes2 = vec![
                    PartialTableauNode::new(id, fml21, from_id),
                    PartialTableauNode::new(id + 1, fml22, from_id),
                ];
                id += 4;
                let is_trivial_1 = seq.is_trivial2(fml11, fml12);
                let is_trivial_2 = seq.is_trivial2(fml21, fml22);

                let mut seq1 = seq.clone();
                let mut seq2 = seq;
                seq1.push(fml11);
                seq1.push(fml12);
                seq2.push(fml21);
                seq2.push(fml22);
                let parent_idx = nodes.len() - 1;
                let new_node1 =
                    ProofNode::new(seq1, parent_idx, formula_map1, local_tableau_nodes1);
                let new_node2 =
                    ProofNode::new(seq2, parent_idx, formula_map2, local_tableau_nodes2);
                if is_trivial_1 {
                    new_node1.children_cnt.set(0).unwrap();
                }
                if is_trivial_2 {
                    new_node2.children_cnt.set(0).unwrap();
                }
                nodes.push(new_node1);
                nodes.push(new_node2);
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
fn flush_proved_nodes<'a>(nodes: &mut Vec<ProofNode<'a>>, forest_nodes: &mut Vec<TableauNode<'a>>) {
    while let Some(node) = nodes.last() {
        // check if the children_cnt has been set
        let Some(children_cnt) = node.children_cnt.get() else {
            // not processed yet
            break;
        };
        if node.proved_children_cnt < *children_cnt {
            // TODO: 2025/08/29 ここって通る？？
            // if has unproved children, stop processing
            break;
        }
        let children_cnt = *children_cnt;

        if let Some(parent_idx) = node.parent_idx {
            // if has a parent
            // increment the parent's proved children count
            nodes[parent_idx].proved_children_cnt += 1;
        }

        // remove the completed node and use it directly
        let mut completed_node = nodes.pop().unwrap();

        // convert all PartialTableauNode to TableauNode and add to forest_nodes
        // The last added tableau node gets the children_cnt value, others get 1
        while let Some(partial_tableau_node) = completed_node.local_tableau_nodes.pop() {
            let current_children_cnt = if completed_node.local_tableau_nodes.is_empty() {
                // This is the last node (which was added first)
                children_cnt
            } else {
                // Other nodes get 1
                1
            };

            let tableau_node = TableauNode::new(
                partial_tableau_node.id,
                partial_tableau_node.fml,
                partial_tableau_node.from_id,
                current_children_cnt,
            );
            forest_nodes.push(tableau_node);
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

        // drain last `children_cnt` subtrees from stack and combine with current node
        for vec in stack.drain(stack.len() - children_cnt..) {
            new_vec.extend(vec);
        }

        // push the new combined subtree back to stack
        stack.push(new_vec);
    }

    // stack should contain exactly one subtree
    assert_eq!(stack.len(), 1);

    stack.pop().unwrap()
}

/// Write forest nodes to LaTeX buffer using stack-based algorithm
/// - Stack tracks remaining children count for each node
/// - Indent management for proper LaTeX formatting
/// - Automatic closing of brackets when children count reaches zero
fn write_latex(forest_nodes: &[TableauNode<'_>], names: &Names, buf: &mut Vec<u8>) {
    // stack of remaining children count
    let mut stack = vec![];
    // current indentation level
    let mut ind = 1;

    for TableauNode {
        id,
        fml,
        from_id,
        children_cnt,
    } in forest_nodes
    {
        check_buf_size(buf);
        if *children_cnt != 0 {
            // internal node - write opening bracket
            check_buf_size(buf);
            if *from_id == 0 {
                writeln!(
                    buf,
                    "{:ind$}[{},idx={id}",
                    "",
                    fml.to_tableau_form().display(names),
                    ind = ind * 2
                )
                .unwrap();
            } else {
                writeln!(
                    buf,
                    "{:ind$}[{},idx={id},from={from_id}",
                    "",
                    fml.to_tableau_form().display(names),
                    ind = ind * 2
                )
                .unwrap();
            }

            // increment indentation for children
            ind += 1;
            // push current node's children count to stack
            stack.push(*children_cnt);
            continue;
        }

        // leaf node - write with close attribute
        if *from_id == 0 {
            writeln!(
                buf,
                "{:ind$}[{},idx={id},close]",
                "",
                fml.to_tableau_form().display(names),
                ind = ind * 2
            )
            .unwrap();
        } else {
            writeln!(
                buf,
                "{:ind$}[{},idx={id},from={from_id},close]",
                "",
                fml.to_tableau_form().display(names),
                ind = ind * 2
            )
            .unwrap();
        }

        // decrement children count of parent on stack
        *stack.last_mut().unwrap() -= 1;

        // process completed nodes on stack
        while let Some(&children_cnt) = stack.last() {
            if children_cnt == 0 {
                // node completed - pop from stack and close bracket
                stack.pop();
                ind -= 1;
                check_buf_size(buf);
                writeln!(buf, "{:ind$}]", "", ind = ind * 2).unwrap();

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
}
