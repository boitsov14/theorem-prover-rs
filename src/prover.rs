use crate::formula::Formula;
use crate::naming::NamingInfo;
use core::hash::BuildHasherDefault;
use indexmap::IndexSet;
use itertools::repeat_n;
use rustc_hash::FxHasher;

type FxIndexSet<T> = IndexSet<T, BuildHasherDefault<FxHasher>>;

/// Sequent of formulae
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct Sequent<'a> {
    pub ant: FxIndexSet<&'a Formula>,
    pub suc: FxIndexSet<&'a Formula>,
}

#[derive(Debug, Clone)]
enum SequentType {
    Ant,
    Suc,
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

#[derive(Debug, Clone)]
struct Tactic {
    pos: usize,
    seq_type: SequentType,
}

impl Tactic {
    fn new(pos: usize, seq_type: SequentType) -> Self {
        Self { pos, seq_type }
    }
    fn dummy() -> Self {
        Self {
            pos: 0,
            seq_type: SequentType::Ant,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ProofState {
    Provable,
    UnProvable,
}

impl<'a> Sequent<'a> {
    #[inline(never)]
    fn get_fml(&mut self) -> Option<(usize, SequentType)> {
        use Formula::*;
        use SequentType::*;
        let mut p_nary = None;
        // TODO: 2023/11/03 rev()を使うかどうか(パフォーマンス要比較)
        // TODO: 2023/11/04 for文4回まわすのとどっちが早いか
        // TODO: 2023/11/07 不要なfmlは削除できるか
        // TODO: 2023/11/07 unaryなものも必要性のチェックをするか
        // TODO: 2023/11/07 リターンはfmlでは難しいか
        for (i, fml) in self.ant.iter().enumerate().rev() {
            match fml {
                Predicate(..) => continue,
                Not(_) | And(_) => {
                    return Some((i, Ant));
                }
                Or(l) => {
                    if p_nary.is_none() && l.iter().all(|p| !self.ant.contains(p)) {
                        p_nary = Some((i, Ant));
                    }
                }
                Implies(p, q) => {
                    if p_nary.is_none() && !self.suc.contains(&**p) && !self.ant.contains(&**q) {
                        p_nary = Some((i, Ant));
                    }
                }
                All(_, _) | Exists(_, _) => unimplemented!(),
            }
        }
        for (i, fml) in self.suc.iter().enumerate().rev() {
            match fml {
                Predicate(..) => continue,
                Not(_) | Or(_) | Implies(..) => {
                    return Some((i, Suc));
                }
                And(l) => {
                    if p_nary.is_none() && l.iter().all(|p| !self.suc.contains(p)) {
                        p_nary = Some((i, Suc));
                    }
                }
                All(_, _) | Exists(_, _) => unimplemented!(),
            }
        }
        p_nary
    }

    #[inline(never)]
    fn apply_tactic(mut self, vec: &mut Vec<(Sequent<'a>, bool)>) -> Option<(Tactic, usize)> {
        use Formula::*;
        use SequentType::*;
        // TODO: 2023/11/07 get_fmlは外出ししたい
        let (pos, seq_type) = self.get_fml()?;
        let n = match seq_type {
            Ant => {
                let fml = self.ant[pos];
                match fml {
                    Not(p) => {
                        self.ant.swap_remove_index(pos);
                        self.suc.insert(p);
                        let is_proved = self.ant.contains(&**p);
                        vec.push((self, is_proved));
                        1
                    }
                    And(l) => {
                        self.ant.swap_remove_index(pos);
                        for p in l {
                            self.ant.insert(p);
                        }
                        let is_proved = l.iter().any(|p| self.suc.contains(p));
                        vec.push((self, is_proved));
                        1
                    }
                    Or(l) => {
                        self.ant.swap_remove_index(pos);
                        for (p, mut seq) in l.iter().rev().zip(repeat_n(self, l.len())) {
                            seq.ant.insert(p);
                            let is_proved = seq.suc.contains(p);
                            vec.push((seq, is_proved));
                        }
                        l.len()
                    }
                    Implies(p, q) => {
                        self.ant.swap_remove_index(pos);
                        let mut seq_l = self.clone();
                        let mut seq_r = self;
                        seq_l.suc.insert(p);
                        let is_proved_l = seq_l.ant.contains(&**p);
                        seq_r.ant.insert(q);
                        let is_proved_r = seq_r.suc.contains(&**q);
                        vec.push((seq_r, is_proved_r));
                        vec.push((seq_l, is_proved_l));
                        2
                    }
                    All(..) | Exists(..) => unimplemented!(),
                    Predicate(..) => unreachable!(),
                }
            }
            Suc => {
                let fml = self.suc[pos];
                match fml {
                    Not(p) => {
                        self.suc.swap_remove_index(pos);
                        self.ant.insert(p);
                        let is_proved = self.suc.contains(&**p);
                        vec.push((self, is_proved));
                        1
                    }
                    And(l) => {
                        self.suc.swap_remove_index(pos);
                        for (p, mut seq) in l.iter().rev().zip(repeat_n(self, l.len())) {
                            seq.suc.insert(p);
                            let is_proved = seq.ant.contains(p);
                            vec.push((seq, is_proved));
                        }
                        l.len()
                    }
                    Or(l) => {
                        self.suc.swap_remove_index(pos);
                        for p in l {
                            self.suc.insert(p);
                        }
                        let is_proved = l.iter().any(|p| self.ant.contains(p));
                        vec.push((self, is_proved));
                        1
                    }
                    Implies(p, q) => {
                        self.suc.swap_remove_index(pos);
                        self.ant.insert(p);
                        self.suc.insert(q);
                        let is_proved = self.suc.contains(&**p) || self.ant.contains(&**q);
                        vec.push((self, is_proved));
                        1
                    }
                    All(..) | Exists(..) => unimplemented!(),
                    Predicate(..) => unreachable!(),
                }
            }
        };
        Some((Tactic::new(pos, seq_type), n))
    }
}

impl Node {
    fn new(tactic: Tactic) -> Self {
        Self {
            tactic,
            subproofs: Vec::with_capacity(2),
        }
    }
    #[inline(never)]
    fn make_proof_tree<'a>(
        &mut self,
        sequent: Sequent<'a>,
        vec: &mut Vec<(Sequent<'a>, bool)>,
    ) -> ProofState {
        use ProofState::*;
        if let Some((tactic, n)) = sequent.apply_tactic(vec) {
            // let Tactic { pos, seq_type } = tactic.clone();
            // let fml = match seq_type {
            //     SequentType::Ant => &sequent.ant[pos],
            //     SequentType::Suc => &sequent.suc[pos],
            // };
            // use Formula::*;
            // let mut sig = match fml {
            //     Not(_) => "¬",
            //     And(_) => "∧",
            //     Or(_) => "∨",
            //     Implies(_, _) => "→",
            //     All(_, _) => "∀",
            //     Exists(_, _) => "∃",
            //     Predicate(_, _) => unreachable!(),
            // }
            // .to_string();
            // if fml.is_iff() {
            //     sig = "↔".to_string();
            // }
            // match seq_type {
            //     SequentType::Ant => {
            //         sig.push_str(": Left");
            //     }
            //     SequentType::Suc => {
            //         sig.push_str(": Right");
            //     }
            // }
            // println!("{}", sig);
            // for (seq, _) in vec.iter().rev() {
            //     println!("{}", &seq.display(inf));
            // }
            let mut node = Node::new(tactic);
            let mut result = Provable;
            for _ in 0..n {
                let (sequent, state) = vec.pop().unwrap();
                if state {
                    // println!("Axiom");
                    // for (seq, _) in vec.iter().rev() {
                    //     println!("{}", &seq.display(inf));
                    // }
                    node.subproofs.push(ProofTree::Leaf(Provable))
                } else {
                    let state0 = node.make_proof_tree(sequent, vec);
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

pub fn example() {
    use crate::parser::parse;
    use std::time::Instant;
    // 625ms -> 7m -> 0.7ms vs 157ms
    // let s = "((o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o31 ∧ o41) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o32 ∧ o42) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o33 ∧ o43))";
    // ? -> 107ms vs 8411ms
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54))";
    // 75,387ms
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14 ∨ o15) ∧ (o21 ∨ o22 ∨ o23 ∨ o24 ∨ o25) ∧ (o31 ∨ o32 ∨ o33 ∨ o34 ∨ o35) ∧ (o41 ∨ o42 ∨ o43 ∨ o44 ∨ o45) ∧ (o51 ∨ o52 ∨ o53 ∨ o54 ∨ o55) ∧ (o61 ∨ o62 ∨ o63 ∨ o64 ∨ o65)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o11 ∧ o61) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o21 ∧ o61) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o31 ∧ o61) ∨ (o41 ∧ o51) ∨ (o41 ∧ o61) ∨ (o51 ∧ o61) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o12 ∧ o62) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o22 ∧ o62) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o32 ∧ o62) ∨ (o42 ∧ o52) ∨ (o42 ∧ o62) ∨(o52 ∧ o62) ∨(o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o13 ∧ o63) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o23 ∧ o63) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o33 ∧ o63) ∨ (o43 ∧ o53) ∨ (o43 ∧ o63) ∨ (o53 ∧ o63) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o14 ∧ o64) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o24 ∧ o64) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o34 ∧ o64) ∨ (o44 ∧ o54) ∨ (o44 ∧ o64) ∨(o54 ∧ o64) ∨ (o15 ∧ o25) ∨ (o15 ∧ o35) ∨ (o15 ∧ o45) ∨ (o15 ∧ o55) ∨ (o15 ∧ o65) ∨ (o25 ∧ o35) ∨ (o25 ∧ o45) ∨ (o25 ∧ o55) ∨ (o25 ∧ o65) ∨ (o35 ∧ o45) ∨ (o35 ∧ o55) ∨ (o35 ∧ o65) ∨ (o45 ∧ o55) ∨ (o45 ∧ o65) ∨(o55 ∧ o65))";
    // 55ms vs Error
    // let s = "(o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43) <-> (o11 ∧ o21 ∧ o31 ∧ o41) ∨ (o11 ∧ o21 ∧ o31 ∧ o42) ∨ (o11 ∧ o21 ∧ o31 ∧ o43) ∨ (o11 ∧ o21 ∧ o32 ∧ o41) ∨ (o11 ∧ o21 ∧ o32 ∧ o42) ∨ (o11 ∧ o21 ∧ o32 ∧ o43) ∨ (o11 ∧ o21 ∧ o33 ∧ o41) ∨ (o11 ∧ o21 ∧ o33 ∧ o42) ∨ (o11 ∧ o21 ∧ o33 ∧ o43) ∨ (o11 ∧ o22 ∧ o31 ∧ o41) ∨ (o11 ∧ o22 ∧ o31 ∧ o42) ∨ (o11 ∧ o22 ∧ o31 ∧ o43) ∨ (o11 ∧ o22 ∧ o32 ∧ o41) ∨ (o11 ∧ o22 ∧ o32 ∧ o42) ∨ (o11 ∧ o22 ∧ o32 ∧ o43) ∨ (o11 ∧ o22 ∧ o33 ∧ o41) ∨ (o11 ∧ o22 ∧ o33 ∧ o42) ∨ (o11 ∧ o22 ∧ o33 ∧ o43) ∨ (o11 ∧ o23 ∧ o31 ∧ o41) ∨ (o11 ∧ o23 ∧ o31 ∧ o42) ∨ (o11 ∧ o23 ∧ o31 ∧ o43) ∨ (o11 ∧ o23 ∧ o32 ∧ o41) ∨ (o11 ∧ o23 ∧ o32 ∧ o42) ∨ (o11 ∧ o23 ∧ o32 ∧ o43) ∨ (o11 ∧ o23 ∧ o33 ∧ o41) ∨ (o11 ∧ o23 ∧ o33 ∧ o42) ∨ (o11 ∧ o23 ∧ o33 ∧ o43) ∨ (o12 ∧ o21 ∧ o31 ∧ o41) ∨ (o12 ∧ o21 ∧ o31 ∧ o42) ∨ (o12 ∧ o21 ∧ o31 ∧ o43) ∨ (o12 ∧ o21 ∧ o32 ∧ o41) ∨ (o12 ∧ o21 ∧ o32 ∧ o42) ∨ (o12 ∧ o21 ∧ o32 ∧ o43) ∨ (o12 ∧ o21 ∧ o33 ∧ o41) ∨ (o12 ∧ o21 ∧ o33 ∧ o42) ∨ (o12 ∧ o21 ∧ o33 ∧ o43) ∨ (o12 ∧ o22 ∧ o31 ∧ o41) ∨ (o12 ∧ o22 ∧ o31 ∧ o42) ∨ (o12 ∧ o22 ∧ o31 ∧ o43) ∨ (o12 ∧ o22 ∧ o32 ∧ o41) ∨ (o12 ∧ o22 ∧ o32 ∧ o42) ∨ (o12 ∧ o22 ∧ o32 ∧ o43) ∨ (o12 ∧ o22 ∧ o33 ∧ o41) ∨ (o12 ∧ o22 ∧ o33 ∧ o42) ∨ (o12 ∧ o22 ∧ o33 ∧ o43) ∨ (o12 ∧ o23 ∧ o31 ∧ o41) ∨ (o12 ∧ o23 ∧ o31 ∧ o42) ∨ (o12 ∧ o23 ∧ o31 ∧ o43) ∨ (o12 ∧ o23 ∧ o32 ∧ o41) ∨ (o12 ∧ o23 ∧ o32 ∧ o42) ∨ (o12 ∧ o23 ∧ o32 ∧ o43) ∨ (o12 ∧ o23 ∧ o33 ∧ o41) ∨ (o12 ∧ o23 ∧ o33 ∧ o42) ∨ (o12 ∧ o23 ∧ o33 ∧ o43) ∨ (o13 ∧ o21 ∧ o31 ∧ o41) ∨ (o13 ∧ o21 ∧ o31 ∧ o42) ∨ (o13 ∧ o21 ∧ o31 ∧ o43) ∨ (o13 ∧ o21 ∧ o32 ∧ o41) ∨ (o13 ∧ o21 ∧ o32 ∧ o42) ∨ (o13 ∧ o21 ∧ o32 ∧ o43) ∨ (o13 ∧ o21 ∧ o33 ∧ o41) ∨ (o13 ∧ o21 ∧ o33 ∧ o42) ∨ (o13 ∧ o21 ∧ o33 ∧ o43) ∨ (o13 ∧ o22 ∧ o31 ∧ o41) ∨ (o13 ∧ o22 ∧ o31 ∧ o42) ∨ (o13 ∧ o22 ∧ o31 ∧ o43) ∨ (o13 ∧ o22 ∧ o32 ∧ o41) ∨ (o13 ∧ o22 ∧ o32 ∧ o42) ∨ (o13 ∧ o22 ∧ o32 ∧ o43) ∨ (o13 ∧ o22 ∧ o33 ∧ o41) ∨ (o13 ∧ o22 ∧ o33 ∧ o42) ∨ (o13 ∧ o22 ∧ o33 ∧ o43) ∨ (o13 ∧ o23 ∧ o31 ∧ o41) ∨ (o13 ∧ o23 ∧ o31 ∧ o42) ∨ (o13 ∧ o23 ∧ o31 ∧ o43) ∨ (o13 ∧ o23 ∧ o32 ∧ o41) ∨ (o13 ∧ o23 ∧ o32 ∧ o42) ∨ (o13 ∧ o23 ∧ o32 ∧ o43) ∨ (o13 ∧ o23 ∧ o33 ∧ o41) ∨ (o13 ∧ o23 ∧ o33 ∧ o42) ∨ (o13 ∧ o23 ∧ o33 ∧ o43)";
    // 152ms -> 220ms vs 1405ms
    // let s = "((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔j))))))))))";
    // 523ms -> 890ms vs 2418ms
    let s = "(((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔k)))))))))))";
    // 1889ms -> 3577ms vs out of memory
    // let s = "((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔l))))))))))))";
    // 6886ms -> 14638ms
    // let s = "(((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔m)))))))))))))";
    // 25,764ms -> 58708ms
    // let s = "((((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔n)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔(m⇔n))))))))))))))";
    // 97,620ms -> ?
    // let s = "(((((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔n)⇔o)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔(m⇔(n⇔o)))))))))))))))";
    // 388,709ms -> ?
    // let s = "((((((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔n)⇔o)⇔p)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔(m⇔(n⇔(o⇔p))))))))))))))))";

    // let s = "P and Q to Q and P";
    // let s = "P or Q to Q or P";
    // let s = "¬(P ∧ Q) ↔ (¬P ∨ ¬Q)";
    // let s = "(((a⇔b)⇔c) -> (a⇔(b⇔c)))";

    let s = "(((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔i)))))))))";

    let Some((fml, inf)) = parse(s) else {
        return;
    };
    let fml = fml.universal_quantify();
    println!("{}", fml.display(&inf));
    let mut node = Node::new(Tactic::dummy());
    let mut seq = Sequent::default();
    seq.suc.insert(&fml);
    let mut vec = vec![];
    let start_time = Instant::now();
    let result = node.make_proof_tree(seq, &mut vec);
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
    assert_eq!(result, ProofState::Provable);
}

pub fn example_for_bench(fml: &Formula) -> ProofState {
    let mut node = Node::new(Tactic::dummy());
    let mut seq = Sequent::default();
    seq.suc.insert(&fml);
    let mut vec = vec![];
    node.make_proof_tree(seq, &mut vec)
}

pub fn example_iltp_prop() {
    use crate::parser::from_tptp;
    use crate::parser::parse;
    use std::fs;
    use std::time::Instant;

    let exclude_list = fs::read_to_string("benches/iltp_prop_exclude.txt").unwrap();
    let exclude_list = exclude_list.lines().collect::<Vec<_>>();

    let entries = fs::read_dir("benches/iltp_prop").unwrap();
    for entry in entries {
        let file = entry.unwrap().path();
        let file_name = file.file_name().unwrap().to_str().unwrap();
        if exclude_list.contains(&file_name) {
            continue;
        }
        println!();
        println!("{file_name}");
        let s = fs::read_to_string(&file).unwrap();
        let (fml, inf) = parse(&from_tptp(&s)).unwrap();
        // println!("{}", fml.display(&inf));
        let start_time = Instant::now();
        let result = example_for_bench(&fml);
        let end_time = Instant::now();
        let elapsed_time = end_time.duration_since(start_time);
        println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
        assert_eq!(result, ProofState::Provable);
    }
}
