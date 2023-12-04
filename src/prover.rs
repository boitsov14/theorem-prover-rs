use crate::formula::Formula;
use crate::naming::{Latex, NamingInfo};
use core::hash::BuildHasherDefault;
use indexmap::IndexSet;
use itertools::repeat_n;
use rustc_hash::FxHasher;
use std::cell::OnceCell;
use std::fs::File;
use std::io::{BufWriter, Result, Write};
use typed_arena::Arena;

type FxIndexSet<T> = IndexSet<T, BuildHasherDefault<FxHasher>>;

/// Sequent of formulae
#[derive(Clone, Debug, Default)]
pub struct Sequent<'a> {
    pub ant: FxIndexSet<&'a Formula>,
    pub suc: FxIndexSet<&'a Formula>,
}

#[derive(Clone, Copy, Debug)]
enum SequentType {
    Ant,
    Suc,
}

#[derive(Debug)]
enum ProofTree<'a> {
    Proved,
    Node {
        tactic: Tactic<'a>,
        subproofs: Vec<ProofTree<'a>>,
    },
    Unresolved(&'a OnceCell<ProofTree<'a>>),
}

#[derive(Debug)]
struct Tactic<'a> {
    fml: &'a Formula,
    seq_type: SequentType,
}

#[derive(Debug)]
enum ProofState {
    Provable,
    UnProvable,
}

#[derive(Clone, Copy, Debug)]
enum OutputType {
    Console,
    Latex,
}

impl<'a> Sequent<'a> {
    fn get_fml(&self) -> Option<(&'a Formula, SequentType)> {
        use Formula::*;
        use SequentType::*;
        for fml in &self.ant {
            match fml {
                Not(_) | And(_) => {
                    return Some((fml, Ant));
                }
                _ => {}
            }
        }
        for fml in &self.suc {
            match fml {
                Not(_) | Or(_) | Implies(..) => {
                    return Some((fml, Suc));
                }
                _ => {}
            }
        }
        for fml in &self.ant {
            match fml {
                Or(l) => {
                    if l.iter().all(|p| !self.ant.contains(p)) {
                        return Some((fml, Ant));
                    }
                }
                Implies(p, q) => {
                    if !self.suc.contains(&**p) && !self.ant.contains(&**q) {
                        return Some((fml, Ant));
                    }
                }
                _ => {}
            }
        }
        for fml in &self.suc {
            match fml {
                And(l) => {
                    if l.iter().all(|p| !self.suc.contains(p)) {
                        return Some((fml, Suc));
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn apply_tactic(
        mut self,
        fml: &'a Formula,
        seq_type: SequentType,
        seqs: &mut Vec<(Sequent<'a>, bool)>,
    ) -> usize {
        use Formula::*;
        use SequentType::*;
        match seq_type {
            Ant => match fml {
                Not(p) => {
                    self.ant.remove(fml);
                    self.suc.insert(p);
                    let is_proved = self.ant.contains(&**p);
                    seqs.push((self, is_proved));
                    1
                }
                And(l) => {
                    self.ant.remove(fml);
                    for p in l {
                        self.ant.insert(p);
                    }
                    let is_proved = l.iter().any(|p| self.suc.contains(p));
                    seqs.push((self, is_proved));
                    1
                }
                Or(l) => {
                    self.ant.remove(fml);
                    for (p, mut seq) in l.iter().rev().zip(repeat_n(self, l.len())) {
                        seq.ant.insert(p);
                        let is_proved = seq.suc.contains(p);
                        seqs.push((seq, is_proved));
                    }
                    l.len()
                }
                Implies(p, q) => {
                    self.ant.remove(fml);
                    let mut seq_l = self.clone();
                    let mut seq_r = self;
                    seq_l.suc.insert(p);
                    let is_proved_l = seq_l.ant.contains(&**p);
                    seq_r.ant.insert(q);
                    let is_proved_r = seq_r.suc.contains(&**q);
                    seqs.push((seq_r, is_proved_r));
                    seqs.push((seq_l, is_proved_l));
                    2
                }
                All(..) | Exists(..) => unimplemented!(),
                Predicate(..) => unreachable!(),
            },
            Suc => match fml {
                Not(p) => {
                    self.suc.remove(fml);
                    self.ant.insert(p);
                    let is_proved = self.suc.contains(&**p);
                    seqs.push((self, is_proved));
                    1
                }
                And(l) => {
                    // TODO: 2023/11/11 trueの場合
                    self.suc.remove(fml);
                    for (p, mut seq) in l.iter().rev().zip(repeat_n(self, l.len())) {
                        seq.suc.insert(p);
                        let is_proved = seq.ant.contains(p);
                        seqs.push((seq, is_proved));
                    }
                    l.len()
                }
                Or(l) => {
                    self.suc.remove(fml);
                    for p in l {
                        self.suc.insert(p);
                    }
                    let is_proved = l.iter().any(|p| self.ant.contains(p));
                    seqs.push((self, is_proved));
                    1
                }
                Implies(p, q) => {
                    self.suc.remove(fml);
                    self.ant.insert(p);
                    self.suc.insert(q);
                    let is_proved = self.suc.contains(&**p) || self.ant.contains(&**q);
                    seqs.push((self, is_proved));
                    1
                }
                All(..) | Exists(..) => unimplemented!(),
                Predicate(..) => unreachable!(),
            },
        }
    }
}

fn prove<'a>(
    seqs: &mut Vec<(Sequent<'a>, bool)>,
    unresolved: &mut Vec<(&'a OnceCell<ProofTree<'a>>, Sequent<'a>)>,
    arena: &'a Arena<OnceCell<ProofTree<'a>>>,
) -> (ProofTree<'a>, bool) {
    use ProofTree::*;
    let (seq, is_proved) = seqs.pop().unwrap();
    if is_proved {
        (Proved, true)
    } else if let Some((fml, seq_type)) = seq.get_fml() {
        let len = seq.apply_tactic(fml, seq_type, seqs);
        let mut subproofs = Vec::with_capacity(len);
        let mut is_proved = true;
        // TODO: 2023/11/30 for文で書くか，iterを使うか
        for _ in 0..len {
            let (tree, is_proved0) = prove(seqs, unresolved, arena);
            subproofs.push(tree);
            if !is_proved0 {
                // TODO: 2023/11/11 Unprovableとわかった時点で探索を終了すべきか
                is_proved = false;
            }
        }
        let tactic = Tactic { fml, seq_type };
        (Node { tactic, subproofs }, is_proved)
    } else {
        let cell = arena.alloc(OnceCell::new());
        let tree = Unresolved(cell);
        unresolved.push((cell, seq));
        (tree, false)
    }
}

impl<'a> ProofTree<'a> {
    fn write_rec(
        &self,
        seqs: &mut Vec<(Sequent<'a>, bool)>,
        inf: &NamingInfo,
        output: OutputType,
        w: &mut BufWriter<impl Write>,
    ) -> Result<()> {
        use OutputType::*;
        use ProofTree::*;
        if matches!(output, Console) {
            for (seq, _) in seqs.iter().rev() {
                writeln!(w, "{}", &seq.display(inf))?;
            }
        }
        let (seq, _) = seqs.pop().unwrap();
        match self {
            Proved => {
                assert!(!seq.ant.is_disjoint(&seq.suc));
                match output {
                    Console => {
                        writeln!(w, "Axiom")?;
                    }
                    Latex => {
                        writeln!(
                            w,
                            r"\infer{{0}}[\scriptsize Axiom]{{{}}}",
                            seq.display(inf).to_latex()
                        )?;
                    }
                }
            }
            // TODO: 2023/12/02 Unresolvedがあとから解決された場合の処理
            Unresolved(_) => match output {
                Console => {
                    writeln!(w, "UnProvable")?;
                }
                Latex => {
                    writeln!(w, r"\hypo{{{}}}", seq.display(inf).to_latex())?;
                }
            },
            Node { tactic, subproofs } => {
                let Tactic { fml, seq_type } = tactic;
                let len = seq.clone().apply_tactic(fml, *seq_type, seqs);
                assert_eq!(len, subproofs.len());
                let label = get_label(fml, seq_type, output);
                if matches!(output, Console) {
                    writeln!(w, "{label}")?;
                }
                for proof in subproofs {
                    proof.write_rec(seqs, inf, output, w)?;
                }
                if matches!(output, Latex) {
                    writeln!(
                        w,
                        r"\infer{{{len}}}[\scriptsize {label}]{{{}}}",
                        seq.display(inf).to_latex()
                    )?;
                }
            }
        }
        Ok(())
    }

    fn write(
        &self,
        fml: &'a Formula,
        inf: &NamingInfo,
        output: OutputType,
        w: &mut BufWriter<impl Write>,
    ) -> Result<()> {
        use OutputType::*;
        let mut seqs = fml.to_seqs();
        if matches!(output, Latex) {
            writeln!(
                w,
                r"\documentclass[preview,varwidth=\maxdimen,border=10pt]{{standalone}}"
            )?;
            writeln!(w, r"\usepackage{{ebproof}}")?;
            writeln!(w, r"\begin{{document}}")?;
            writeln!(w, r"\begin{{prooftree}}")?;
        }
        self.write_rec(&mut seqs, &inf, output, w)?;
        assert!(seqs.is_empty());
        if matches!(output, Latex) {
            writeln!(w, r"\end{{prooftree}}")?;
            writeln!(w, r"\end{{document}}")?;
        }
        Ok(())
    }
}

fn get_label(fml: &Formula, seq_type: &SequentType, output: OutputType) -> String {
    use Formula::*;
    use OutputType::*;
    let fml_type = match fml {
        Not(_) => match output {
            Console => "¬",
            Latex => r"$\lnot$",
        },
        And(l) => match l.as_slice() {
            [] => match output {
                Console => "true",
                Latex => r"$\top$",
            },
            [Implies(p_l, q_l), Implies(p_r, q_r)] if p_l == q_r && q_l == p_r => match output {
                Console => "↔",
                Latex => r"$\leftrightarrow$",
            },
            _ => match output {
                Console => "∧",
                Latex => r"$\land$",
            },
        },
        Or(l) => match l.as_slice() {
            [] => match output {
                Console => "false",
                Latex => r"$\bot$",
            },
            _ => match output {
                Console => "∨",
                Latex => r"$\lor$",
            },
        },
        Implies(..) => match output {
            Console => "→",
            Latex => r"$\rightarrow$",
        },
        All(..) => match output {
            Console => "∀",
            Latex => r"$\forall$",
        },
        Exists(..) => match output {
            Console => "∃",
            Latex => r"$\exists$",
        },
        Predicate(..) => unreachable!(),
    };
    let seq_type = match seq_type {
        SequentType::Ant => ": Left",
        SequentType::Suc => ": Right",
    };
    format!("{fml_type}{seq_type}")
}

impl Formula {
    fn to_seqs(&self) -> Vec<(Sequent, bool)> {
        let mut seq = Sequent::default();
        seq.suc.insert(self);
        vec![(seq, false)]
    }

    fn prove<'a>(&'a self, arena: &'a Arena<OnceCell<ProofTree<'a>>>) -> (ProofTree, bool) {
        let mut seqs = self.to_seqs();
        let mut seqs_waiting = vec![];
        let (tree, is_proved) = prove(&mut seqs, &mut seqs_waiting, &arena);
        // println!("------");
        // println!("{is_proved}");
        // println!("{}", seqs.len());
        // println!("{:#?}", tree);
        // println!("------");
        // for (cell, seq) in seqs_waiting {
        //     println!("{:#?}", seq);
        //     let tactic = Tactic {
        //         fml: self,
        //         seq_type: SequentType::Ant,
        //     };
        //     let tree = ProofTree::Node {
        //         tactic,
        //         subproofs: vec![],
        //     };
        //     cell.set(tree).unwrap();
        // }
        // println!("------");
        // println!("{:#?}", tree);
        // println!("------");
        (tree, is_proved)
    }

    pub fn assert_provable(&self) {
        let arena = Arena::new();
        let (_, is_proved) = self.prove(&arena);
        assert!(is_proved);
    }
}

pub fn example() -> Result<()> {
    use crate::parser::parse;
    use std::time::Instant;
    // 107ms vs 8411ms
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54))";
    // 83,264ms
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14 ∨ o15) ∧ (o21 ∨ o22 ∨ o23 ∨ o24 ∨ o25) ∧ (o31 ∨ o32 ∨ o33 ∨ o34 ∨ o35) ∧ (o41 ∨ o42 ∨ o43 ∨ o44 ∨ o45) ∧ (o51 ∨ o52 ∨ o53 ∨ o54 ∨ o55) ∧ (o61 ∨ o62 ∨ o63 ∨ o64 ∨ o65)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o11 ∧ o61) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o21 ∧ o61) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o31 ∧ o61) ∨ (o41 ∧ o51) ∨ (o41 ∧ o61) ∨ (o51 ∧ o61) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o12 ∧ o62) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o22 ∧ o62) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o32 ∧ o62) ∨ (o42 ∧ o52) ∨ (o42 ∧ o62) ∨(o52 ∧ o62) ∨(o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o13 ∧ o63) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o23 ∧ o63) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o33 ∧ o63) ∨ (o43 ∧ o53) ∨ (o43 ∧ o63) ∨ (o53 ∧ o63) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o14 ∧ o64) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o24 ∧ o64) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o34 ∧ o64) ∨ (o44 ∧ o54) ∨ (o44 ∧ o64) ∨(o54 ∧ o64) ∨ (o15 ∧ o25) ∨ (o15 ∧ o35) ∨ (o15 ∧ o45) ∨ (o15 ∧ o55) ∨ (o15 ∧ o65) ∨ (o25 ∧ o35) ∨ (o25 ∧ o45) ∨ (o25 ∧ o55) ∨ (o25 ∧ o65) ∨ (o35 ∧ o45) ∨ (o35 ∧ o55) ∨ (o35 ∧ o65) ∨ (o45 ∧ o55) ∨ (o45 ∧ o65) ∨(o55 ∧ o65))";
    // 46ms vs Error
    // let s = "(o11 ∨ o12 ∨ o13) ∧ (o21 ∨ o22 ∨ o23) ∧ (o31 ∨ o32 ∨ o33) ∧ (o41 ∨ o42 ∨ o43) <-> (o11 ∧ o21 ∧ o31 ∧ o41) ∨ (o11 ∧ o21 ∧ o31 ∧ o42) ∨ (o11 ∧ o21 ∧ o31 ∧ o43) ∨ (o11 ∧ o21 ∧ o32 ∧ o41) ∨ (o11 ∧ o21 ∧ o32 ∧ o42) ∨ (o11 ∧ o21 ∧ o32 ∧ o43) ∨ (o11 ∧ o21 ∧ o33 ∧ o41) ∨ (o11 ∧ o21 ∧ o33 ∧ o42) ∨ (o11 ∧ o21 ∧ o33 ∧ o43) ∨ (o11 ∧ o22 ∧ o31 ∧ o41) ∨ (o11 ∧ o22 ∧ o31 ∧ o42) ∨ (o11 ∧ o22 ∧ o31 ∧ o43) ∨ (o11 ∧ o22 ∧ o32 ∧ o41) ∨ (o11 ∧ o22 ∧ o32 ∧ o42) ∨ (o11 ∧ o22 ∧ o32 ∧ o43) ∨ (o11 ∧ o22 ∧ o33 ∧ o41) ∨ (o11 ∧ o22 ∧ o33 ∧ o42) ∨ (o11 ∧ o22 ∧ o33 ∧ o43) ∨ (o11 ∧ o23 ∧ o31 ∧ o41) ∨ (o11 ∧ o23 ∧ o31 ∧ o42) ∨ (o11 ∧ o23 ∧ o31 ∧ o43) ∨ (o11 ∧ o23 ∧ o32 ∧ o41) ∨ (o11 ∧ o23 ∧ o32 ∧ o42) ∨ (o11 ∧ o23 ∧ o32 ∧ o43) ∨ (o11 ∧ o23 ∧ o33 ∧ o41) ∨ (o11 ∧ o23 ∧ o33 ∧ o42) ∨ (o11 ∧ o23 ∧ o33 ∧ o43) ∨ (o12 ∧ o21 ∧ o31 ∧ o41) ∨ (o12 ∧ o21 ∧ o31 ∧ o42) ∨ (o12 ∧ o21 ∧ o31 ∧ o43) ∨ (o12 ∧ o21 ∧ o32 ∧ o41) ∨ (o12 ∧ o21 ∧ o32 ∧ o42) ∨ (o12 ∧ o21 ∧ o32 ∧ o43) ∨ (o12 ∧ o21 ∧ o33 ∧ o41) ∨ (o12 ∧ o21 ∧ o33 ∧ o42) ∨ (o12 ∧ o21 ∧ o33 ∧ o43) ∨ (o12 ∧ o22 ∧ o31 ∧ o41) ∨ (o12 ∧ o22 ∧ o31 ∧ o42) ∨ (o12 ∧ o22 ∧ o31 ∧ o43) ∨ (o12 ∧ o22 ∧ o32 ∧ o41) ∨ (o12 ∧ o22 ∧ o32 ∧ o42) ∨ (o12 ∧ o22 ∧ o32 ∧ o43) ∨ (o12 ∧ o22 ∧ o33 ∧ o41) ∨ (o12 ∧ o22 ∧ o33 ∧ o42) ∨ (o12 ∧ o22 ∧ o33 ∧ o43) ∨ (o12 ∧ o23 ∧ o31 ∧ o41) ∨ (o12 ∧ o23 ∧ o31 ∧ o42) ∨ (o12 ∧ o23 ∧ o31 ∧ o43) ∨ (o12 ∧ o23 ∧ o32 ∧ o41) ∨ (o12 ∧ o23 ∧ o32 ∧ o42) ∨ (o12 ∧ o23 ∧ o32 ∧ o43) ∨ (o12 ∧ o23 ∧ o33 ∧ o41) ∨ (o12 ∧ o23 ∧ o33 ∧ o42) ∨ (o12 ∧ o23 ∧ o33 ∧ o43) ∨ (o13 ∧ o21 ∧ o31 ∧ o41) ∨ (o13 ∧ o21 ∧ o31 ∧ o42) ∨ (o13 ∧ o21 ∧ o31 ∧ o43) ∨ (o13 ∧ o21 ∧ o32 ∧ o41) ∨ (o13 ∧ o21 ∧ o32 ∧ o42) ∨ (o13 ∧ o21 ∧ o32 ∧ o43) ∨ (o13 ∧ o21 ∧ o33 ∧ o41) ∨ (o13 ∧ o21 ∧ o33 ∧ o42) ∨ (o13 ∧ o21 ∧ o33 ∧ o43) ∨ (o13 ∧ o22 ∧ o31 ∧ o41) ∨ (o13 ∧ o22 ∧ o31 ∧ o42) ∨ (o13 ∧ o22 ∧ o31 ∧ o43) ∨ (o13 ∧ o22 ∧ o32 ∧ o41) ∨ (o13 ∧ o22 ∧ o32 ∧ o42) ∨ (o13 ∧ o22 ∧ o32 ∧ o43) ∨ (o13 ∧ o22 ∧ o33 ∧ o41) ∨ (o13 ∧ o22 ∧ o33 ∧ o42) ∨ (o13 ∧ o22 ∧ o33 ∧ o43) ∨ (o13 ∧ o23 ∧ o31 ∧ o41) ∨ (o13 ∧ o23 ∧ o31 ∧ o42) ∨ (o13 ∧ o23 ∧ o31 ∧ o43) ∨ (o13 ∧ o23 ∧ o32 ∧ o41) ∨ (o13 ∧ o23 ∧ o32 ∧ o42) ∨ (o13 ∧ o23 ∧ o32 ∧ o43) ∨ (o13 ∧ o23 ∧ o33 ∧ o41) ∨ (o13 ∧ o23 ∧ o33 ∧ o42) ∨ (o13 ∧ o23 ∧ o33 ∧ o43)";
    // 233ms vs 1405ms
    // let s = "((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔j))))))))))";
    // 817ms vs 2418ms
    // let s = "(((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔k)))))))))))";
    // 2,965ms vs out of memory
    // let s = "((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔l))))))))))))";
    // 10,567ms
    // let s = "(((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔m)))))))))))))";
    // 38,633ms
    // let s = "((((((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔l)⇔m)⇔n)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔(k⇔(l⇔(m⇔n))))))))))))))";

    let s = "P and Q to Q and P";
    // let s = "P or Q to Q or P";
    // let s = "¬(P ∧ Q) ↔ (¬P ∨ ¬Q)";
    // let s = "(a⇔b)⇔(b⇔a)";

    // let s = "P to true";
    // let s = "P to false";
    // let s = "false to P";
    // let s = "true to P";

    // parse
    let (fml, inf) = parse(s).unwrap();
    let fml = fml.universal_quantify();
    println!("{}", fml.display(&inf));

    // prove
    let arena = Arena::new();
    let start_time = Instant::now();
    let (proof, is_proved) = fml.prove(&arena);
    let end_time = Instant::now();
    println!(">> {is_proved:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
    assert!(is_proved);

    // print console
    let mut w = BufWriter::new(vec![]);
    proof.write(&fml, &inf, OutputType::Console, &mut w)?;
    println!("{}", String::from_utf8_lossy(&w.into_inner()?));

    // write latex
    let f = File::create("proof.tex")?;
    let mut w = BufWriter::new(f);
    proof.write(&fml, &inf, OutputType::Latex, &mut w)?;

    Ok(())
}

pub fn example_iltp_prop() {
    use crate::parser::from_tptp;
    use crate::parser::parse;
    use std::fs;
    use std::time::Instant;

    let exclude_list = fs::read_to_string("benches/iltp_prop/exclude.txt").unwrap();
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
        let arena = Arena::new();
        let start_time = Instant::now();
        let (_, is_proved) = fml.prove(&arena);
        let end_time = Instant::now();
        let elapsed_time = end_time.duration_since(start_time);
        println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
        assert!(is_proved);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use insta::assert_snapshot;

    #[test]
    fn test_latex1() {
        assert_snapshot!(prove("P"));
    }

    #[test]
    fn test_latex2() {
        assert_snapshot!(prove("not not P to P"));
    }

    #[test]
    fn test_latex3() {
        assert_snapshot!(prove("P and Q and R to R and Q and P"));
    }

    #[test]
    fn test_latex4() {
        assert_snapshot!(prove("P or Q or R to R or Q or P"));
    }

    #[test]
    fn test_latex5() {
        assert_snapshot!(prove("P to (P to Q) to (Q to R) to R"));
    }

    #[test]
    fn test_latex6() {
        assert_snapshot!(prove("(P iff Q) to (Q iff P)"));
    }

    #[test]
    fn test_latex7() {
        assert_snapshot!(prove("P to true"));
    }

    #[test]
    fn test_latex8() {
        assert_snapshot!(prove("P to false"));
    }

    #[test]
    fn test_latex9() {
        assert_snapshot!(prove("true to P"));
    }

    #[test]
    fn test_latex10() {
        assert_snapshot!(prove("false to P"));
    }

    #[test]
    fn test_latex11() {
        assert_snapshot!(prove("(o11 ∨ o12) → ((o21 ∨ o22) → ((o31 ∨ o32) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o21 ∧ o31) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o22 ∧ o32))))"));
    }

    #[test]
    fn test_latex12() {
        assert_snapshot!(prove("((a1 ↔ a2) ↔ a3) ↔ (a3 ↔ (a2 ↔ a1))"));
    }

    fn prove(s: &str) -> String {
        // parse
        let (fml, inf) = parse(s).unwrap();
        let fml = fml.universal_quantify();
        // prove
        let arena = Arena::new();
        let (proof, _) = fml.prove(&arena);
        // latex
        let mut w = BufWriter::new(vec![]);
        proof.write(&fml, &inf, OutputType::Latex, &mut w).unwrap();
        String::from_utf8(w.into_inner().unwrap()).unwrap()
    }
}
