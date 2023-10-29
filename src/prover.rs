use indexmap::IndexSet;

use crate::formula::{Formula, Term};

use crate::naming::NamingInfo;
use core::hash::BuildHasherDefault;
use itertools::repeat_n;
use rustc_hash::FxHasher;
use strum::{EnumIter, IntoEnumIterator};

type FxIndexSet<T> = IndexSet<T, BuildHasherDefault<FxHasher>>;

/// Structured set of formulae
#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct Formulae<'a> {
    predicate_set: FxIndexSet<(usize, &'a Vec<Term>)>,
    not_set: FxIndexSet<&'a Formula>,
    and_set: FxIndexSet<&'a Vec<Formula>>,
    or_set: FxIndexSet<&'a Vec<Formula>>,
    implies_set: FxIndexSet<(&'a Formula, &'a Formula)>,
    all_set: FxIndexSet<(&'a Vec<usize>, &'a Formula)>,
    exists_set: FxIndexSet<(&'a Vec<usize>, &'a Formula)>,
}

/// Sequent of structured formulae
#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct Sequent<'a> {
    ant: Formulae<'a>,
    suc: Formulae<'a>,
}

/// Sequent of formulae
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlainSequent<'a> {
    pub ant: FxIndexSet<&'a Formula>,
    pub suc: FxIndexSet<&'a Formula>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, EnumIter)]
enum Tactic {
    LNot,
    RNot,
    RImplies,
    LAnd,
    ROr,
    LImplies,
    RAnd,
    LOr,
}

#[derive(Debug)]
enum ProofTree {
    Leaf(ProofState),
    Node(Node),
}

#[derive(Debug)]
struct Node {
    tactic: Tactic,
    subproofs: Vec<ProofTree>,
}

#[derive(Debug, PartialEq)]
enum ProofState {
    Provable,
    UnProvable,
}

impl<'a> Sequent<'a> {
    #[inline(never)]
    fn insert_to_ant(&mut self, fml: &'a Formula) -> bool {
        match fml {
            Formula::Predicate(id, terms) => {
                let p = (*id, terms);
                if self.suc.predicate_set.contains(&p) {
                    self.ant.predicate_set.insert(p);
                    return true;
                }
                self.ant.predicate_set.insert(p);
            }
            Formula::Not(p) => {
                self.ant.not_set.insert(p);
            }
            Formula::And(l) => {
                self.ant.and_set.insert(l);
            }
            Formula::Or(l) => {
                // TODO: 2023/10/10 pがF_FALSEかどうかの判定をする？
                self.ant.or_set.insert(l);
            }
            Formula::Implies(p, q) => {
                self.ant.implies_set.insert((p, q));
            }
            Formula::All(vs, p) => {
                self.ant.all_set.insert((vs, p));
            }
            Formula::Exists(vs, p) => {
                self.ant.exists_set.insert((vs, p));
            }
        }
        false
    }
    #[inline(never)]
    fn insert_to_suc(&mut self, fml: &'a Formula) -> bool {
        match fml {
            Formula::Predicate(id, terms) => {
                let p = (*id, terms);
                if self.ant.predicate_set.contains(&p) {
                    self.suc.predicate_set.insert(p);
                    return true;
                }
                self.suc.predicate_set.insert(p);
            }
            Formula::Not(p) => {
                self.suc.not_set.insert(p);
            }
            Formula::And(l) => {
                self.suc.and_set.insert(l);
            }
            Formula::Or(l) => {
                self.suc.or_set.insert(l);
            }
            Formula::Implies(p, q) => {
                self.suc.implies_set.insert((p, q));
            }
            Formula::All(vs, p) => {
                self.suc.all_set.insert((vs, p));
            }
            Formula::Exists(vs, p) => {
                self.suc.exists_set.insert((vs, p));
            }
        }
        false
    }
    #[inline(never)]
    fn apply_tactic(self) -> Option<TacticResult<'a>> {
        for tactic in Tactic::iter() {
            if tactic.applicable(&self) {
                return Some(TacticResult::new(tactic, tactic.apply(self)));
            }
        }
        None
    }
}

struct TacticResult<'a> {
    tactic: Tactic,
    sequents: Vec<(Sequent<'a>, bool)>,
}

impl<'a> TacticResult<'a> {
    fn new(tactic: Tactic, sequents: Vec<(Sequent<'a>, bool)>) -> Self {
        Self { tactic, sequents }
    }
}

impl Tactic {
    #[inline(never)]
    fn apply(self, mut sequent: Sequent) -> Vec<(Sequent, bool)> {
        use Tactic::*;
        match self {
            LNot => {
                let p = sequent.ant.not_set.pop().unwrap();
                let state = sequent.insert_to_suc(p);
                vec![(sequent, state)]
            }
            RNot => {
                let p = sequent.suc.not_set.pop().unwrap();
                let state = sequent.insert_to_ant(p);
                vec![(sequent, state)]
            }
            RImplies => {
                let (p, q) = sequent.suc.implies_set.pop().unwrap();
                let state = sequent.insert_to_ant(p) | sequent.insert_to_suc(q);
                vec![(sequent, state)]
            }
            LAnd => {
                let l = sequent.ant.and_set.pop().unwrap();
                let mut state = false;
                for p in l {
                    if sequent.insert_to_ant(p) {
                        state = true;
                    }
                }
                vec![(sequent, state)]
            }
            ROr => {
                let l = sequent.suc.or_set.pop().unwrap();
                let mut state = false;
                for p in l {
                    if sequent.insert_to_suc(p) {
                        state = true;
                    }
                }
                vec![(sequent, state)]
            }
            LImplies => {
                let (p, q) = sequent.ant.implies_set.pop().unwrap();
                let mut sequent_l = sequent.clone();
                let mut sequent_r = sequent;
                let state_l = sequent_l.insert_to_suc(p);
                let state_r = sequent_r.insert_to_ant(q);
                vec![(sequent_l, state_l), (sequent_r, state_r)]
            }
            RAnd => {
                let l = sequent.suc.and_set.pop().unwrap();
                let n = l.len();
                let l = l.iter().zip(repeat_n(sequent, n));
                let mut sequents = Vec::with_capacity(n);
                for (p, mut sequent) in l {
                    let state = sequent.insert_to_suc(p);
                    sequents.push((sequent, state));
                }
                sequents
            }
            LOr => {
                let l = sequent.ant.or_set.pop().unwrap();
                let n = l.len();
                let l = l.iter().zip(repeat_n(sequent, n));
                let mut sequents = Vec::with_capacity(n);
                for (p, mut sequent) in l {
                    let state = sequent.insert_to_ant(p);
                    sequents.push((sequent, state));
                }
                sequents
            }
        }
    }
    #[inline(never)]
    fn applicable(&self, sequent: &Sequent) -> bool {
        use Tactic::*;
        match self {
            LNot => !sequent.ant.not_set.is_empty(),
            RNot => !sequent.suc.not_set.is_empty(),
            RImplies => !sequent.suc.implies_set.is_empty(),
            LAnd => !sequent.ant.and_set.is_empty(),
            ROr => !sequent.suc.or_set.is_empty(),
            LImplies => !sequent.ant.implies_set.is_empty(),
            RAnd => !sequent.suc.and_set.is_empty(),
            LOr => !sequent.ant.or_set.is_empty(),
        }
    }

    fn apply_plain(self, mut sequent: PlainSequent) -> Vec<PlainSequent> {
        use Formula::*;
        use Tactic::*;
        match self {
            LNot => {
                for fml in sequent.ant.iter().rev() {
                    if let Not(p) = fml {
                        sequent.ant.shift_remove(*fml);
                        sequent.suc.insert(p);
                        return vec![sequent];
                    }
                }
            }
            RNot => {
                for fml in sequent.suc.iter().rev() {
                    if let Not(p) = fml {
                        sequent.suc.shift_remove(*fml);
                        sequent.ant.insert(p);
                        return vec![sequent];
                    }
                }
            }
            RImplies => {
                for fml in sequent.suc.iter().rev() {
                    if let Implies(p, q) = fml {
                        sequent.suc.shift_remove(*fml);
                        sequent.ant.insert(p);
                        sequent.suc.insert(q);
                        return vec![sequent];
                    }
                }
            }
            LAnd => {
                for fml in sequent.ant.iter().rev() {
                    if let And(l) = fml {
                        sequent.ant.shift_remove(*fml);
                        for p in l {
                            sequent.ant.insert(p);
                        }
                        return vec![sequent];
                    }
                }
            }
            ROr => {
                for fml in sequent.suc.iter().rev() {
                    if let Or(l) = fml {
                        sequent.suc.shift_remove(*fml);
                        for p in l {
                            sequent.suc.insert(p);
                        }
                        return vec![sequent];
                    }
                }
            }
            LImplies => {
                for fml in sequent.ant.iter().rev() {
                    if let Implies(p, q) = fml {
                        sequent.ant.shift_remove(*fml);
                        let mut sequent_l = sequent.clone();
                        let mut sequent_r = sequent;
                        sequent_l.suc.insert(p);
                        sequent_r.ant.insert(q);
                        return vec![sequent_l, sequent_r];
                    }
                }
            }
            RAnd => {
                for fml in sequent.suc.iter().rev() {
                    if let And(l) = fml {
                        sequent.suc.shift_remove(*fml);
                        let n = l.len();
                        let l = l.iter().zip(repeat_n(sequent, n));
                        let mut sequents = Vec::with_capacity(n);
                        for (p, mut sequent) in l {
                            sequent.suc.insert(p);
                            sequents.push(sequent);
                        }
                        return sequents;
                    }
                }
            }
            LOr => {
                for fml in sequent.ant.iter().rev() {
                    if let Or(l) = fml {
                        sequent.ant.shift_remove(*fml);
                        let n = l.len();
                        let l = l.iter().zip(repeat_n(sequent, n));
                        let mut sequents = Vec::with_capacity(n);
                        for (p, mut sequent) in l {
                            sequent.ant.insert(p);
                            sequents.push(sequent);
                        }
                        return sequents;
                    }
                }
            }
        }
        unreachable!();
    }
}

impl Node {
    fn new(tactic: Tactic) -> Self {
        Self {
            tactic,
            subproofs: vec![],
        }
    }
    #[inline(never)]
    fn make_proof_tree(&mut self, sequent: Sequent) -> ProofState {
        use ProofState::*;
        if let Some(TacticResult { tactic, sequents }) = sequent.apply_tactic() {
            let mut node = Node::new(tactic);
            let mut result = Provable;
            for (sequent, state) in sequents {
                if state {
                    node.subproofs.push(ProofTree::Leaf(Provable))
                } else {
                    let state0 = node.make_proof_tree(sequent);
                    if state0 == UnProvable {
                        result = UnProvable;
                    }
                }
            }
            self.subproofs.push(ProofTree::Node(node));
            result
        } else {
            self.subproofs.push(ProofTree::Leaf(UnProvable));
            UnProvable
        }
    }
}

impl ProofTree {
    fn traverse(&self, sequents: &mut Vec<PlainSequent>, inf: &NamingInfo) {
        use ProofTree::*;
        for sequent in sequents.iter().rev() {
            println!("{}", sequent.display(inf));
        }
        let sequent = sequents.pop().unwrap();
        match self {
            Leaf(state) => {
                use ProofState::*;
                match state {
                    Provable => {
                        println!("Axiom");
                        assert!(!sequent.ant.is_disjoint(&sequent.suc));
                    }
                    _ => {
                        println!("{state:?}");
                    }
                }
            }
            Node(node) => {
                println!("{:?}", node.tactic);
                let new_sequents: Vec<_> =
                    node.tactic.apply_plain(sequent).into_iter().rev().collect();
                sequents.extend(new_sequents);
                for tree in &node.subproofs {
                    tree.traverse(sequents, inf);
                }
            }
        }
    }
}

pub fn example() {
    use crate::parser::parse;
    use std::time::Instant;
    // 1081ms vs 157ms
    // let s = "((o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o31 ∧ o41) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o32 ∧ o42) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o33 ∧ o43))";
    // ? vs 8411ms
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54))";
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14 ∨ o15) ∧ (o21 ∨ o22 ∨ o23 ∨ o24 ∨ o25) ∧ (o31 ∨ o32 ∨ o33 ∨ o34 ∨ o35) ∧ (o41 ∨ o42 ∨ o43 ∨ o44 ∨ o45) ∧ (o51 ∨ o52 ∨ o53 ∨ o54 ∨ o55)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54) ∨ (o15 ∧ o25) ∨ (o15 ∧ o35) ∨ (o15 ∧ o45) ∨ (o15 ∧ o55) ∨ (o25 ∧ o35) ∨ (o25 ∧ o45) ∨ (o25 ∧ o55) ∨ (o35 ∧ o45) ∨ (o35 ∧ o55) ∨ (o45 ∧ o55))";
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14 ∨ o15 ∨ o16) ∧ (o21 ∨ o22 ∨ o23 ∨ o24 ∨ o25 ∨ o26) ∧ (o31 ∨ o32 ∨ o33 ∨ o34 ∨ o35 ∨ o36) ∧ (o41 ∨ o42 ∨ o43 ∨ o44 ∨ o45 ∨ o46) ∧ (o51 ∨ o52 ∨ o53 ∨ o54 ∨ o55 ∨ o56) ∧ (o61 ∨ o62 ∨ o63 ∨ o64 ∨ o65 ∨ o66)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o11 ∧ o61) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o21 ∧ o61) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o31 ∧ o61) ∨ (o41 ∧ o51) ∨ (o41 ∧ o61) ∨ (o51 ∧ o61) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o12 ∧ o62) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o22 ∧ o62) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o32 ∧ o62) ∨ (o42 ∧ o52) ∨ (o42 ∧ o62) ∨ (o52 ∧ o62) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o13 ∧ o63) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o23 ∧ o63) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o33 ∧ o63) ∨ (o43 ∧ o53) ∨ (o43 ∧ o63) ∨ (o53 ∧ o63) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o14 ∧ o64) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o24 ∧ o64) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o34 ∧ o64) ∨ (o44 ∧ o54) ∨ (o44 ∧ o64) ∨ (o54 ∧ o64) ∨ (o15 ∧ o25) ∨ (o15 ∧ o35) ∨ (o15 ∧ o45) ∨ (o15 ∧ o55) ∨ (o15 ∧ o65) ∨ (o25 ∧ o35) ∨ (o25 ∧ o45) ∨ (o25 ∧ o55) ∨ (o25 ∧ o65) ∨ (o35 ∧ o45) ∨ (o35 ∧ o55) ∨ (o35 ∧ o65) ∨ (o45 ∧ o55) ∨ (o45 ∧ o65) ∨ (o55 ∧ o65) ∨ (o16 ∧ o26) ∨ (o16 ∧ o36) ∨ (o16 ∧ o46) ∨ (o16 ∧ o56) ∨ (o16 ∧ o66) ∨ (o26 ∧ o36) ∨ (o26 ∧ o46) ∨ (o26 ∧ o56) ∨ (o26 ∧ o66) ∨ (o36 ∧ o46) ∨ (o36 ∧ o56) ∨ (o36 ∧ o66) ∨ (o46 ∧ o56) ∨ (o46 ∧ o66) ∨ (o56 ∧ o66))";
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14 ∨ o15 ∨ o16 ∨ o17) ∧ (o21 ∨ o22 ∨ o23 ∨ o24 ∨ o25 ∨ o26 ∨ o27) ∧ (o31 ∨ o32 ∨ o33 ∨ o34 ∨ o35 ∨ o36 ∨ o37) ∧ (o41 ∨ o42 ∨ o43 ∨ o44 ∨ o45 ∨ o46 ∨ o47) ∧ (o51 ∨ o52 ∨ o53 ∨ o54 ∨ o55 ∨ o56 ∨ o57) ∧ (o61 ∨ o62 ∨ o63 ∨ o64 ∨ o65 ∨ o66 ∨ o67) ∧ (o71 ∨ o72 ∨ o73 ∨ o74 ∨ o75 ∨ o76 ∨ o77)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o11 ∧ o61) ∨ (o11 ∧ o71) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o21 ∧ o61) ∨ (o21 ∧ o71) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o31 ∧ o61) ∨ (o31 ∧ o71) ∨ (o41 ∧ o51) ∨ (o41 ∧ o61) ∨ (o41 ∧ o71) ∨ (o51 ∧ o61) ∨ (o51 ∧ o71) ∨ (o61 ∧ o71) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o12 ∧ o62) ∨ (o12 ∧ o72) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o22 ∧ o62) ∨ (o22 ∧ o72) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o32 ∧ o62) ∨ (o32 ∧ o72) ∨ (o42 ∧ o52) ∨ (o42 ∧ o62) ∨ (o42 ∧ o72) ∨ (o52 ∧ o62) ∨ (o52 ∧ o72) ∨ (o62 ∧ o72) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o13 ∧ o63) ∨ (o13 ∧ o73) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o23 ∧ o63) ∨ (o23 ∧ o73) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o33 ∧ o63) ∨ (o33 ∧ o73) ∨ (o43 ∧ o53) ∨ (o43 ∧ o63) ∨ (o43 ∧ o73) ∨ (o53 ∧ o63) ∨ (o53 ∧ o73) ∨ (o63 ∧ o73) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o14 ∧ o64) ∨ (o14 ∧ o74) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o24 ∧ o64) ∨ (o24 ∧ o74) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o34 ∧ o64) ∨ (o34 ∧ o74) ∨ (o44 ∧ o54) ∨ (o44 ∧ o64) ∨ (o44 ∧ o74) ∨ (o54 ∧ o64) ∨ (o54 ∧ o74) ∨ (o64 ∧ o74) ∨ (o15 ∧ o25) ∨ (o15 ∧ o35) ∨ (o15 ∧ o45) ∨ (o15 ∧ o55) ∨ (o15 ∧ o65) ∨ (o15 ∧ o75) ∨ (o25 ∧ o35) ∨ (o25 ∧ o45) ∨ (o25 ∧ o55) ∨ (o25 ∧ o65) ∨ (o25 ∧ o75) ∨ (o35 ∧ o45) ∨ (o35 ∧ o55) ∨ (o35 ∧ o65) ∨ (o35 ∧ o75) ∨ (o45 ∧ o55) ∨ (o45 ∧ o65) ∨ (o45 ∧ o75) ∨ (o55 ∧ o65) ∨ (o55 ∧ o75) ∨ (o65 ∧ o75) ∨ (o16 ∧ o26) ∨ (o16 ∧ o36) ∨ (o16 ∧ o46) ∨ (o16 ∧ o56) ∨ (o16 ∧ o66) ∨ (o16 ∧ o76) ∨ (o26 ∧ o36) ∨ (o26 ∧ o46) ∨ (o26 ∧ o56) ∨ (o26 ∧ o66) ∨ (o26 ∧ o76) ∨ (o36 ∧ o46) ∨ (o36 ∧ o56) ∨ (o36 ∧ o66) ∨ (o36 ∧ o76) ∨ (o46 ∧ o56) ∨ (o46 ∧ o66) ∨ (o46 ∧ o76) ∨ (o56 ∧ o66) ∨ (o56 ∧ o76) ∨ (o66 ∧ o76) ∨ (o17 ∧ o27) ∨ (o17 ∧ o37) ∨ (o17 ∧ o47) ∨ (o17 ∧ o57) ∨ (o17 ∧ o67) ∨ (o17 ∧ o77) ∨ (o27 ∧ o37) ∨ (o27 ∧ o47) ∨ (o27 ∧ o57) ∨ (o27 ∧ o67) ∨ (o27 ∧ o77) ∨ (o37 ∧ o47) ∨ (o37 ∧ o57) ∨ (o37 ∧ o67) ∨ (o37 ∧ o77) ∨ (o47 ∧ o57) ∨ (o47 ∧ o67) ∨ (o47 ∧ o77) ∨ (o57 ∧ o67) ∨ (o57 ∧ o77) ∨ (o67 ∧ o77))";
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14 ∨ o15 ∨ o16 ∨ o17 ∨ o18) ∧ (o21 ∨ o22 ∨ o23 ∨ o24 ∨ o25 ∨ o26 ∨ o27 ∨ o28) ∧ (o31 ∨ o32 ∨ o33 ∨ o34 ∨ o35 ∨ o36 ∨ o37 ∨ o38) ∧ (o41 ∨ o42 ∨ o43 ∨ o44 ∨ o45 ∨ o46 ∨ o47 ∨ o48) ∧ (o51 ∨ o52 ∨ o53 ∨ o54 ∨ o55 ∨ o56 ∨ o57 ∨ o58) ∧ (o61 ∨ o62 ∨ o63 ∨ o64 ∨ o65 ∨ o66 ∨ o67 ∨ o68) ∧ (o71 ∨ o72 ∨ o73 ∨ o74 ∨ o75 ∨ o76 ∨ o77 ∨ o78) ∧ (o81 ∨ o82 ∨ o83 ∨ o84 ∨ o85 ∨ o86 ∨ o87 ∨ o88)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o11 ∧ o61) ∨ (o11 ∧ o71) ∨ (o11 ∧ o81) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o21 ∧ o61) ∨ (o21 ∧ o71) ∨ (o21 ∧ o81) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o31 ∧ o61) ∨ (o31 ∧ o71) ∨ (o31 ∧ o81) ∨ (o41 ∧ o51) ∨ (o41 ∧ o61) ∨ (o41 ∧ o71) ∨ (o41 ∧ o81) ∨ (o51 ∧ o61) ∨ (o51 ∧ o71) ∨ (o51 ∧ o81) ∨ (o61 ∧ o71) ∨ (o61 ∧ o81) ∨ (o71 ∧ o81) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o12 ∧ o62) ∨ (o12 ∧ o72) ∨ (o12 ∧ o82) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o22 ∧ o62) ∨ (o22 ∧ o72) ∨ (o22 ∧ o82) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o32 ∧ o62) ∨ (o32 ∧ o72) ∨ (o32 ∧ o82) ∨ (o42 ∧ o52) ∨ (o42 ∧ o62) ∨ (o42 ∧ o72) ∨ (o42 ∧ o82) ∨ (o52 ∧ o62) ∨ (o52 ∧ o72) ∨ (o52 ∧ o82) ∨ (o62 ∧ o72) ∨ (o62 ∧ o82) ∨ (o72 ∧ o82) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o13 ∧ o63) ∨ (o13 ∧ o73) ∨ (o13 ∧ o83) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o23 ∧ o63) ∨ (o23 ∧ o73) ∨ (o23 ∧ o83) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o33 ∧ o63) ∨ (o33 ∧ o73) ∨ (o33 ∧ o83) ∨ (o43 ∧ o53) ∨ (o43 ∧ o63) ∨ (o43 ∧ o73) ∨ (o43 ∧ o83) ∨ (o53 ∧ o63) ∨ (o53 ∧ o73) ∨ (o53 ∧ o83) ∨ (o63 ∧ o73) ∨ (o63 ∧ o83) ∨ (o73 ∧ o83) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o14 ∧ o64) ∨ (o14 ∧ o74) ∨ (o14 ∧ o84) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o24 ∧ o64) ∨ (o24 ∧ o74) ∨ (o24 ∧ o84) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o34 ∧ o64) ∨ (o34 ∧ o74) ∨ (o34 ∧ o84) ∨ (o44 ∧ o54) ∨ (o44 ∧ o64) ∨ (o44 ∧ o74) ∨ (o44 ∧ o84) ∨ (o54 ∧ o64) ∨ (o54 ∧ o74) ∨ (o54 ∧ o84) ∨ (o64 ∧ o74) ∨ (o64 ∧ o84) ∨ (o74 ∧ o84) ∨ (o15 ∧ o25) ∨ (o15 ∧ o35) ∨ (o15 ∧ o45) ∨ (o15 ∧ o55) ∨ (o15 ∧ o65) ∨ (o15 ∧ o75) ∨ (o15 ∧ o85) ∨ (o25 ∧ o35) ∨ (o25 ∧ o45) ∨ (o25 ∧ o55) ∨ (o25 ∧ o65) ∨ (o25 ∧ o75) ∨ (o25 ∧ o85) ∨ (o35 ∧ o45) ∨ (o35 ∧ o55) ∨ (o35 ∧ o65) ∨ (o35 ∧ o75) ∨ (o35 ∧ o85) ∨ (o45 ∧ o55) ∨ (o45 ∧ o65) ∨ (o45 ∧ o75) ∨ (o45 ∧ o85) ∨ (o55 ∧ o65) ∨ (o55 ∧ o75) ∨ (o55 ∧ o85) ∨ (o65 ∧ o75) ∨ (o65 ∧ o85) ∨ (o75 ∧ o85) ∨ (o16 ∧ o26) ∨ (o16 ∧ o36) ∨ (o16 ∧ o46) ∨ (o16 ∧ o56) ∨ (o16 ∧ o66) ∨ (o16 ∧ o76) ∨ (o16 ∧ o86) ∨ (o26 ∧ o36) ∨ (o26 ∧ o46) ∨ (o26 ∧ o56) ∨ (o26 ∧ o66) ∨ (o26 ∧ o76) ∨ (o26 ∧ o86) ∨ (o36 ∧ o46) ∨ (o36 ∧ o56) ∨ (o36 ∧ o66) ∨ (o36 ∧ o76) ∨ (o36 ∧ o86) ∨ (o46 ∧ o56) ∨ (o46 ∧ o66) ∨ (o46 ∧ o76) ∨ (o46 ∧ o86) ∨ (o56 ∧ o66) ∨ (o56 ∧ o76) ∨ (o56 ∧ o86) ∨ (o66 ∧ o76) ∨ (o66 ∧ o86) ∨ (o76 ∧ o86) ∨ (o17 ∧ o27) ∨ (o17 ∧ o37) ∨ (o17 ∧ o47) ∨ (o17 ∧ o57) ∨ (o17 ∧ o67) ∨ (o17 ∧ o77) ∨ (o17 ∧ o87) ∨ (o27 ∧ o37) ∨ (o27 ∧ o47) ∨ (o27 ∧ o57) ∨ (o27 ∧ o67) ∨ (o27 ∧ o77) ∨ (o27 ∧ o87) ∨ (o37 ∧ o47) ∨ (o37 ∧ o57) ∨ (o37 ∧ o67) ∨ (o37 ∧ o77) ∨ (o37 ∧ o87) ∨ (o47 ∧ o57) ∨ (o47 ∧ o67) ∨ (o47 ∧ o77) ∨ (o47 ∧ o87) ∨ (o57 ∧ o67) ∨ (o57 ∧ o77) ∨ (o57 ∧ o87) ∨ (o67 ∧ o77) ∨ (o67 ∧ o87) ∨ (o77 ∧ o87) ∨ (o18 ∧ o28) ∨ (o18 ∧ o38) ∨ (o18 ∧ o48) ∨ (o18 ∧ o58) ∨ (o18 ∧ o68) ∨ (o18 ∧ o78) ∨ (o18 ∧ o88) ∨ (o28 ∧ o38) ∨ (o28 ∧ o48) ∨ (o28 ∧ o58) ∨ (o28 ∧ o68) ∨ (o28 ∧ o78) ∨ (o28 ∧ o88) ∨ (o38 ∧ o48) ∨ (o38 ∧ o58) ∨ (o38 ∧ o68) ∨ (o38 ∧ o78) ∨ (o38 ∧ o88) ∨ (o48 ∧ o58) ∨ (o48 ∧ o68) ∨ (o48 ∧ o78) ∨ (o48 ∧ o88) ∨ (o58 ∧ o68) ∨ (o58 ∧ o78) ∨ (o58 ∧ o88) ∨ (o68 ∧ o78) ∨ (o68 ∧ o88) ∨ (o78 ∧ o88))";
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14 ∨ o15 ∨ o16 ∨ o17 ∨ o18 ∨ o19) ∧ (o21 ∨ o22 ∨ o23 ∨ o24 ∨ o25 ∨ o26 ∨ o27 ∨ o28 ∨ o29) ∧ (o31 ∨ o32 ∨ o33 ∨ o34 ∨ o35 ∨ o36 ∨ o37 ∨ o38 ∨ o39) ∧ (o41 ∨ o42 ∨ o43 ∨ o44 ∨ o45 ∨ o46 ∨ o47 ∨ o48 ∨ o49) ∧ (o51 ∨ o52 ∨ o53 ∨ o54 ∨ o55 ∨ o56 ∨ o57 ∨ o58 ∨ o59) ∧ (o61 ∨ o62 ∨ o63 ∨ o64 ∨ o65 ∨ o66 ∨ o67 ∨ o68 ∨ o69) ∧ (o71 ∨ o72 ∨ o73 ∨ o74 ∨ o75 ∨ o76 ∨ o77 ∨ o78 ∨ o79) ∧ (o81 ∨ o82 ∨ o83 ∨ o84 ∨ o85 ∨ o86 ∨ o87 ∨ o88 ∨ o89) ∧ (o91 ∨ o92 ∨ o93 ∨ o94 ∨ o95 ∨ o96 ∨ o97 ∨ o98 ∨ o99)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o11 ∧ o61) ∨ (o11 ∧ o71) ∨ (o11 ∧ o81) ∨ (o11 ∧ o91) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o21 ∧ o61) ∨ (o21 ∧ o71) ∨ (o21 ∧ o81) ∨ (o21 ∧ o91) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o31 ∧ o61) ∨ (o31 ∧ o71) ∨ (o31 ∧ o81) ∨ (o31 ∧ o91) ∨ (o41 ∧ o51) ∨ (o41 ∧ o61) ∨ (o41 ∧ o71) ∨ (o41 ∧ o81) ∨ (o41 ∧ o91) ∨ (o51 ∧ o61) ∨ (o51 ∧ o71) ∨ (o51 ∧ o81) ∨ (o51 ∧ o91) ∨ (o61 ∧ o71) ∨ (o61 ∧ o81) ∨ (o61 ∧ o91) ∨ (o71 ∧ o81) ∨ (o71 ∧ o91) ∨ (o81 ∧ o91) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o12 ∧ o62) ∨ (o12 ∧ o72) ∨ (o12 ∧ o82) ∨ (o12 ∧ o92) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o22 ∧ o62) ∨ (o22 ∧ o72) ∨ (o22 ∧ o82) ∨ (o22 ∧ o92) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o32 ∧ o62) ∨ (o32 ∧ o72) ∨ (o32 ∧ o82) ∨ (o32 ∧ o92) ∨ (o42 ∧ o52) ∨ (o42 ∧ o62) ∨ (o42 ∧ o72) ∨ (o42 ∧ o82) ∨ (o42 ∧ o92) ∨ (o52 ∧ o62) ∨ (o52 ∧ o72) ∨ (o52 ∧ o82) ∨ (o52 ∧ o92) ∨ (o62 ∧ o72) ∨ (o62 ∧ o82) ∨ (o62 ∧ o92) ∨ (o72 ∧ o82) ∨ (o72 ∧ o92) ∨ (o82 ∧ o92) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o13 ∧ o63) ∨ (o13 ∧ o73) ∨ (o13 ∧ o83) ∨ (o13 ∧ o93) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o23 ∧ o63) ∨ (o23 ∧ o73) ∨ (o23 ∧ o83) ∨ (o23 ∧ o93) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o33 ∧ o63) ∨ (o33 ∧ o73) ∨ (o33 ∧ o83) ∨ (o33 ∧ o93) ∨ (o43 ∧ o53) ∨ (o43 ∧ o63) ∨ (o43 ∧ o73) ∨ (o43 ∧ o83) ∨ (o43 ∧ o93) ∨ (o53 ∧ o63) ∨ (o53 ∧ o73) ∨ (o53 ∧ o83) ∨ (o53 ∧ o93) ∨ (o63 ∧ o73) ∨ (o63 ∧ o83) ∨ (o63 ∧ o93) ∨ (o73 ∧ o83) ∨ (o73 ∧ o93) ∨ (o83 ∧ o93) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o14 ∧ o64) ∨ (o14 ∧ o74) ∨ (o14 ∧ o84) ∨ (o14 ∧ o94) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o24 ∧ o64) ∨ (o24 ∧ o74) ∨ (o24 ∧ o84) ∨ (o24 ∧ o94) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o34 ∧ o64) ∨ (o34 ∧ o74) ∨ (o34 ∧ o84) ∨ (o34 ∧ o94) ∨ (o44 ∧ o54) ∨ (o44 ∧ o64) ∨ (o44 ∧ o74) ∨ (o44 ∧ o84) ∨ (o44 ∧ o94) ∨ (o54 ∧ o64) ∨ (o54 ∧ o74) ∨ (o54 ∧ o84) ∨ (o54 ∧ o94) ∨ (o64 ∧ o74) ∨ (o64 ∧ o84) ∨ (o64 ∧ o94) ∨ (o74 ∧ o84) ∨ (o74 ∧ o94) ∨ (o84 ∧ o94) ∨ (o15 ∧ o25) ∨ (o15 ∧ o35) ∨ (o15 ∧ o45) ∨ (o15 ∧ o55) ∨ (o15 ∧ o65) ∨ (o15 ∧ o75) ∨ (o15 ∧ o85) ∨ (o15 ∧ o95) ∨ (o25 ∧ o35) ∨ (o25 ∧ o45) ∨ (o25 ∧ o55) ∨ (o25 ∧ o65) ∨ (o25 ∧ o75) ∨ (o25 ∧ o85) ∨ (o25 ∧ o95) ∨ (o35 ∧ o45) ∨ (o35 ∧ o55) ∨ (o35 ∧ o65) ∨ (o35 ∧ o75) ∨ (o35 ∧ o85) ∨ (o35 ∧ o95) ∨ (o45 ∧ o55) ∨ (o45 ∧ o65) ∨ (o45 ∧ o75) ∨ (o45 ∧ o85) ∨ (o45 ∧ o95) ∨ (o55 ∧ o65) ∨ (o55 ∧ o75) ∨ (o55 ∧ o85) ∨ (o55 ∧ o95) ∨ (o65 ∧ o75) ∨ (o65 ∧ o85) ∨ (o65 ∧ o95) ∨ (o75 ∧ o85) ∨ (o75 ∧ o95) ∨ (o85 ∧ o95) ∨ (o16 ∧ o26) ∨ (o16 ∧ o36) ∨ (o16 ∧ o46) ∨ (o16 ∧ o56) ∨ (o16 ∧ o66) ∨ (o16 ∧ o76) ∨ (o16 ∧ o86) ∨ (o16 ∧ o96) ∨ (o26 ∧ o36) ∨ (o26 ∧ o46) ∨ (o26 ∧ o56) ∨ (o26 ∧ o66) ∨ (o26 ∧ o76) ∨ (o26 ∧ o86) ∨ (o26 ∧ o96) ∨ (o36 ∧ o46) ∨ (o36 ∧ o56) ∨ (o36 ∧ o66) ∨ (o36 ∧ o76) ∨ (o36 ∧ o86) ∨ (o36 ∧ o96) ∨ (o46 ∧ o56) ∨ (o46 ∧ o66) ∨ (o46 ∧ o76) ∨ (o46 ∧ o86) ∨ (o46 ∧ o96) ∨ (o56 ∧ o66) ∨ (o56 ∧ o76) ∨ (o56 ∧ o86) ∨ (o56 ∧ o96) ∨ (o66 ∧ o76) ∨ (o66 ∧ o86) ∨ (o66 ∧ o96) ∨ (o76 ∧ o86) ∨ (o76 ∧ o96) ∨ (o86 ∧ o96) ∨ (o17 ∧ o27) ∨ (o17 ∧ o37) ∨ (o17 ∧ o47) ∨ (o17 ∧ o57) ∨ (o17 ∧ o67) ∨ (o17 ∧ o77) ∨ (o17 ∧ o87) ∨ (o17 ∧ o97) ∨ (o27 ∧ o37) ∨ (o27 ∧ o47) ∨ (o27 ∧ o57) ∨ (o27 ∧ o67) ∨ (o27 ∧ o77) ∨ (o27 ∧ o87) ∨ (o27 ∧ o97) ∨ (o37 ∧ o47) ∨ (o37 ∧ o57) ∨ (o37 ∧ o67) ∨ (o37 ∧ o77) ∨ (o37 ∧ o87) ∨ (o37 ∧ o97) ∨ (o47 ∧ o57) ∨ (o47 ∧ o67) ∨ (o47 ∧ o77) ∨ (o47 ∧ o87) ∨ (o47 ∧ o97) ∨ (o57 ∧ o67) ∨ (o57 ∧ o77) ∨ (o57 ∧ o87) ∨ (o57 ∧ o97) ∨ (o67 ∧ o77) ∨ (o67 ∧ o87) ∨ (o67 ∧ o97) ∨ (o77 ∧ o87) ∨ (o77 ∧ o97) ∨ (o87 ∧ o97) ∨ (o18 ∧ o28) ∨ (o18 ∧ o38) ∨ (o18 ∧ o48) ∨ (o18 ∧ o58) ∨ (o18 ∧ o68) ∨ (o18 ∧ o78) ∨ (o18 ∧ o88) ∨ (o18 ∧ o98) ∨ (o28 ∧ o38) ∨ (o28 ∧ o48) ∨ (o28 ∧ o58) ∨ (o28 ∧ o68) ∨ (o28 ∧ o78) ∨ (o28 ∧ o88) ∨ (o28 ∧ o98) ∨ (o38 ∧ o48) ∨ (o38 ∧ o58) ∨ (o38 ∧ o68) ∨ (o38 ∧ o78) ∨ (o38 ∧ o88) ∨ (o38 ∧ o98) ∨ (o48 ∧ o58) ∨ (o48 ∧ o68) ∨ (o48 ∧ o78) ∨ (o48 ∧ o88) ∨ (o48 ∧ o98) ∨ (o58 ∧ o68) ∨ (o58 ∧ o78) ∨ (o58 ∧ o88) ∨ (o58 ∧ o98) ∨ (o68 ∧ o78) ∨ (o68 ∧ o88) ∨ (o68 ∧ o98) ∨ (o78 ∧ o88) ∨ (o78 ∧ o98) ∨ (o88 ∧ o98) ∨ (o19 ∧ o29) ∨ (o19 ∧ o39) ∨ (o19 ∧ o49) ∨ (o19 ∧ o59) ∨ (o19 ∧ o69) ∨ (o19 ∧ o79) ∨ (o19 ∧ o89) ∨ (o19 ∧ o99) ∨ (o29 ∧ o39) ∨ (o29 ∧ o49) ∨ (o29 ∧ o59) ∨ (o29 ∧ o69) ∨ (o29 ∧ o79) ∨ (o29 ∧ o89) ∨ (o29 ∧ o99) ∨ (o39 ∧ o49) ∨ (o39 ∧ o59) ∨ (o39 ∧ o69) ∨ (o39 ∧ o79) ∨ (o39 ∧ o89) ∨ (o39 ∧ o99) ∨ (o49 ∧ o59) ∨ (o49 ∧ o69) ∨ (o49 ∧ o79) ∨ (o49 ∧ o89) ∨ (o49 ∧ o99) ∨ (o59 ∧ o69) ∨ (o59 ∧ o79) ∨ (o59 ∧ o89) ∨ (o59 ∧ o99) ∨ (o69 ∧ o79) ∨ (o69 ∧ o89) ∨ (o69 ∧ o99) ∨ (o79 ∧ o89) ∨ (o79 ∧ o99) ∨ (o89 ∧ o99))";
    // fast
    // let s = "not (P and Q and R and S and T and U and V and W and X and Y and Z) to (not P or not Q or not R or not S or not T or not U or not V or not W or not X or not Y or not Z)";
    // let s = "((n1→c1)∧(p2→c1)∧(p2→c2)∧(n3→c2)∧(n4→c2)∧(c1→c2→m)∧((p4→m)→q4)∧((n4→m)→q4)∧((p3→q4)→q3)∧((n3→q4)→q3)∧((p2→q3)→q2)∧((n3→q3)→q2)∧((p1→q2)→q1)∧((n3→q2)→q1)) → q1";
    // 2.1ms vs 110ms
    // let s = "(((((a⇔b)⇔c)⇔d)⇔e)⇔(a⇔(b⇔(c⇔(d⇔e)))))";
    // 9ms vs 170ms
    // let s = "((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔(a⇔(b⇔(c⇔(d⇔(e⇔f))))))";
    // 45ms vs 180ms
    // let s = "(((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔g)))))))";
    // 354ms vs 303ms
    let s = "((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔h))))))))";
    // 5665ms vs 523ms
    // let s = "(((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔i)))))))))";
    // ? vs Error
    // let s = "(o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43) -> (o11 ∧ o21 ∧ o31 ∧ o41) ∨ (o11 ∧ o21 ∧ o31 ∧ o42) ∨ (o11 ∧ o21 ∧ o31 ∧ o43) ∨ (o11 ∧ o21 ∧ o32 ∧ o41) ∨ (o11 ∧ o21 ∧ o32 ∧ o42) ∨ (o11 ∧ o21 ∧ o32 ∧ o43) ∨ (o11 ∧ o21 ∧ o33 ∧ o41) ∨ (o11 ∧ o21 ∧ o33 ∧ o42) ∨ (o11 ∧ o21 ∧ o33 ∧ o43) ∨ (o11 ∧ o22 ∧ o31 ∧ o41) ∨ (o11 ∧ o22 ∧ o31 ∧ o42) ∨ (o11 ∧ o22 ∧ o31 ∧ o43) ∨ (o11 ∧ o22 ∧ o32 ∧ o41) ∨ (o11 ∧ o22 ∧ o32 ∧ o42) ∨ (o11 ∧ o22 ∧ o32 ∧ o43) ∨ (o11 ∧ o22 ∧ o33 ∧ o41) ∨ (o11 ∧ o22 ∧ o33 ∧ o42) ∨ (o11 ∧ o22 ∧ o33 ∧ o43) ∨ (o11 ∧ o23 ∧ o31 ∧ o41) ∨ (o11 ∧ o23 ∧ o31 ∧ o42) ∨ (o11 ∧ o23 ∧ o31 ∧ o43) ∨ (o11 ∧ o23 ∧ o32 ∧ o41) ∨ (o11 ∧ o23 ∧ o32 ∧ o42) ∨ (o11 ∧ o23 ∧ o32 ∧ o43) ∨ (o11 ∧ o23 ∧ o33 ∧ o41) ∨ (o11 ∧ o23 ∧ o33 ∧ o42) ∨ (o11 ∧ o23 ∧ o33 ∧ o43) ∨ (o12 ∧ o21 ∧ o31 ∧ o41) ∨ (o12 ∧ o21 ∧ o31 ∧ o42) ∨ (o12 ∧ o21 ∧ o31 ∧ o43) ∨ (o12 ∧ o21 ∧ o32 ∧ o41) ∨ (o12 ∧ o21 ∧ o32 ∧ o42) ∨ (o12 ∧ o21 ∧ o32 ∧ o43) ∨ (o12 ∧ o21 ∧ o33 ∧ o41) ∨ (o12 ∧ o21 ∧ o33 ∧ o42) ∨ (o12 ∧ o21 ∧ o33 ∧ o43) ∨ (o12 ∧ o22 ∧ o31 ∧ o41) ∨ (o12 ∧ o22 ∧ o31 ∧ o42) ∨ (o12 ∧ o22 ∧ o31 ∧ o43) ∨ (o12 ∧ o22 ∧ o32 ∧ o41) ∨ (o12 ∧ o22 ∧ o32 ∧ o42) ∨ (o12 ∧ o22 ∧ o32 ∧ o43) ∨ (o12 ∧ o22 ∧ o33 ∧ o41) ∨ (o12 ∧ o22 ∧ o33 ∧ o42) ∨ (o12 ∧ o22 ∧ o33 ∧ o43) ∨ (o12 ∧ o23 ∧ o31 ∧ o41) ∨ (o12 ∧ o23 ∧ o31 ∧ o42) ∨ (o12 ∧ o23 ∧ o31 ∧ o43) ∨ (o12 ∧ o23 ∧ o32 ∧ o41) ∨ (o12 ∧ o23 ∧ o32 ∧ o42) ∨ (o12 ∧ o23 ∧ o32 ∧ o43) ∨ (o12 ∧ o23 ∧ o33 ∧ o41) ∨ (o12 ∧ o23 ∧ o33 ∧ o42) ∨ (o12 ∧ o23 ∧ o33 ∧ o43) ∨ (o13 ∧ o21 ∧ o31 ∧ o41) ∨ (o13 ∧ o21 ∧ o31 ∧ o42) ∨ (o13 ∧ o21 ∧ o31 ∧ o43) ∨ (o13 ∧ o21 ∧ o32 ∧ o41) ∨ (o13 ∧ o21 ∧ o32 ∧ o42) ∨ (o13 ∧ o21 ∧ o32 ∧ o43) ∨ (o13 ∧ o21 ∧ o33 ∧ o41) ∨ (o13 ∧ o21 ∧ o33 ∧ o42) ∨ (o13 ∧ o21 ∧ o33 ∧ o43) ∨ (o13 ∧ o22 ∧ o31 ∧ o41) ∨ (o13 ∧ o22 ∧ o31 ∧ o42) ∨ (o13 ∧ o22 ∧ o31 ∧ o43) ∨ (o13 ∧ o22 ∧ o32 ∧ o41) ∨ (o13 ∧ o22 ∧ o32 ∧ o42) ∨ (o13 ∧ o22 ∧ o32 ∧ o43) ∨ (o13 ∧ o22 ∧ o33 ∧ o41) ∨ (o13 ∧ o22 ∧ o33 ∧ o42) ∨ (o13 ∧ o22 ∧ o33 ∧ o43) ∨ (o13 ∧ o23 ∧ o31 ∧ o41) ∨ (o13 ∧ o23 ∧ o31 ∧ o42) ∨ (o13 ∧ o23 ∧ o31 ∧ o43) ∨ (o13 ∧ o23 ∧ o32 ∧ o41) ∨ (o13 ∧ o23 ∧ o32 ∧ o42) ∨ (o13 ∧ o23 ∧ o32 ∧ o43) ∨ (o13 ∧ o23 ∧ o33 ∧ o41) ∨ (o13 ∧ o23 ∧ o33 ∧ o42) ∨ (o13 ∧ o23 ∧ o33 ∧ o43)";
    // let s = "(o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43) <-> (o11 ∧ o21 ∧ o31 ∧ o41) ∨ (o11 ∧ o21 ∧ o31 ∧ o42) ∨ (o11 ∧ o21 ∧ o31 ∧ o43) ∨ (o11 ∧ o21 ∧ o32 ∧ o41) ∨ (o11 ∧ o21 ∧ o32 ∧ o42) ∨ (o11 ∧ o21 ∧ o32 ∧ o43) ∨ (o11 ∧ o21 ∧ o33 ∧ o41) ∨ (o11 ∧ o21 ∧ o33 ∧ o42) ∨ (o11 ∧ o21 ∧ o33 ∧ o43) ∨ (o11 ∧ o22 ∧ o31 ∧ o41) ∨ (o11 ∧ o22 ∧ o31 ∧ o42) ∨ (o11 ∧ o22 ∧ o31 ∧ o43) ∨ (o11 ∧ o22 ∧ o32 ∧ o41) ∨ (o11 ∧ o22 ∧ o32 ∧ o42) ∨ (o11 ∧ o22 ∧ o32 ∧ o43) ∨ (o11 ∧ o22 ∧ o33 ∧ o41) ∨ (o11 ∧ o22 ∧ o33 ∧ o42) ∨ (o11 ∧ o22 ∧ o33 ∧ o43) ∨ (o11 ∧ o23 ∧ o31 ∧ o41) ∨ (o11 ∧ o23 ∧ o31 ∧ o42) ∨ (o11 ∧ o23 ∧ o31 ∧ o43) ∨ (o11 ∧ o23 ∧ o32 ∧ o41) ∨ (o11 ∧ o23 ∧ o32 ∧ o42) ∨ (o11 ∧ o23 ∧ o32 ∧ o43) ∨ (o11 ∧ o23 ∧ o33 ∧ o41) ∨ (o11 ∧ o23 ∧ o33 ∧ o42) ∨ (o11 ∧ o23 ∧ o33 ∧ o43) ∨ (o12 ∧ o21 ∧ o31 ∧ o41) ∨ (o12 ∧ o21 ∧ o31 ∧ o42) ∨ (o12 ∧ o21 ∧ o31 ∧ o43) ∨ (o12 ∧ o21 ∧ o32 ∧ o41) ∨ (o12 ∧ o21 ∧ o32 ∧ o42) ∨ (o12 ∧ o21 ∧ o32 ∧ o43) ∨ (o12 ∧ o21 ∧ o33 ∧ o41) ∨ (o12 ∧ o21 ∧ o33 ∧ o42) ∨ (o12 ∧ o21 ∧ o33 ∧ o43) ∨ (o12 ∧ o22 ∧ o31 ∧ o41) ∨ (o12 ∧ o22 ∧ o31 ∧ o42) ∨ (o12 ∧ o22 ∧ o31 ∧ o43) ∨ (o12 ∧ o22 ∧ o32 ∧ o41) ∨ (o12 ∧ o22 ∧ o32 ∧ o42) ∨ (o12 ∧ o22 ∧ o32 ∧ o43) ∨ (o12 ∧ o22 ∧ o33 ∧ o41) ∨ (o12 ∧ o22 ∧ o33 ∧ o42) ∨ (o12 ∧ o22 ∧ o33 ∧ o43) ∨ (o12 ∧ o23 ∧ o31 ∧ o41) ∨ (o12 ∧ o23 ∧ o31 ∧ o42) ∨ (o12 ∧ o23 ∧ o31 ∧ o43) ∨ (o12 ∧ o23 ∧ o32 ∧ o41) ∨ (o12 ∧ o23 ∧ o32 ∧ o42) ∨ (o12 ∧ o23 ∧ o32 ∧ o43) ∨ (o12 ∧ o23 ∧ o33 ∧ o41) ∨ (o12 ∧ o23 ∧ o33 ∧ o42) ∨ (o12 ∧ o23 ∧ o33 ∧ o43) ∨ (o13 ∧ o21 ∧ o31 ∧ o41) ∨ (o13 ∧ o21 ∧ o31 ∧ o42) ∨ (o13 ∧ o21 ∧ o31 ∧ o43) ∨ (o13 ∧ o21 ∧ o32 ∧ o41) ∨ (o13 ∧ o21 ∧ o32 ∧ o42) ∨ (o13 ∧ o21 ∧ o32 ∧ o43) ∨ (o13 ∧ o21 ∧ o33 ∧ o41) ∨ (o13 ∧ o21 ∧ o33 ∧ o42) ∨ (o13 ∧ o21 ∧ o33 ∧ o43) ∨ (o13 ∧ o22 ∧ o31 ∧ o41) ∨ (o13 ∧ o22 ∧ o31 ∧ o42) ∨ (o13 ∧ o22 ∧ o31 ∧ o43) ∨ (o13 ∧ o22 ∧ o32 ∧ o41) ∨ (o13 ∧ o22 ∧ o32 ∧ o42) ∨ (o13 ∧ o22 ∧ o32 ∧ o43) ∨ (o13 ∧ o22 ∧ o33 ∧ o41) ∨ (o13 ∧ o22 ∧ o33 ∧ o42) ∨ (o13 ∧ o22 ∧ o33 ∧ o43) ∨ (o13 ∧ o23 ∧ o31 ∧ o41) ∨ (o13 ∧ o23 ∧ o31 ∧ o42) ∨ (o13 ∧ o23 ∧ o31 ∧ o43) ∨ (o13 ∧ o23 ∧ o32 ∧ o41) ∨ (o13 ∧ o23 ∧ o32 ∧ o42) ∨ (o13 ∧ o23 ∧ o32 ∧ o43) ∨ (o13 ∧ o23 ∧ o33 ∧ o41) ∨ (o13 ∧ o23 ∧ o33 ∧ o42) ∨ (o13 ∧ o23 ∧ o33 ∧ o43)";

    // let s = "P and Q to Q and P";
    // let s = "¬(P ∧ Q) ↔ (¬P ∨ ¬Q)";
    // let s = "(((a⇔b)⇔c) -> (a⇔(b⇔c)))";

    let Some((fml, inf)) = parse(s) else {
        return;
    };
    let fml = fml.universal_quantify();
    println!("{}", fml.display(&inf));
    let mut node = Node::new(Tactic::LNot);
    let mut sequent = Sequent::default();
    // let arena = Arena::new();
    // let fml = arena.alloc(fml);
    sequent.insert_to_suc(&fml);
    let start_time = Instant::now();
    let result = node.make_proof_tree(sequent);
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("{result:?}");
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
    return;
    let mut suc = FxIndexSet::default();
    suc.insert(&fml);
    let plain_sequent = PlainSequent {
        ant: FxIndexSet::default(),
        suc,
    };
    let start_time = Instant::now();
    node.subproofs[0].traverse(&mut vec![plain_sequent], &inf);
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
}
