use crate::formula::Formula;
use crate::naming::{EntitiesInfo, Latex};
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
    pub fv: Vec<usize>,
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
                Not(_) | And(_) | Exists(..) => {
                    return Some((fml, Ant));
                }
                _ => {}
            }
        }
        for fml in &self.suc {
            match fml {
                Not(_) | Or(_) | Implies(..) | All(..) => {
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
                Exists(vs, p) => {
                    self.ant.remove(fml);
                    todo!()
                }
                All(..) => unimplemented!(),
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
                All(..) => {
                    self.suc.remove(fml);
                    todo!()
                }
                Exists(..) => unimplemented!(),
                Predicate(..) => unreachable!(),
            },
        }
    }
}

fn prove<'a>(
    seqs: &mut Vec<(Sequent<'a>, bool)>,
    unresolved: &mut Vec<(&'a OnceCell<ProofTree<'a>>, Sequent<'a>)>,
    fml_arena: &'a Arena<Formula>,
    tree_arena: &'a Arena<OnceCell<ProofTree<'a>>>,
    entities: &mut EntitiesInfo,
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
            let (tree, is_proved0) = prove(seqs, unresolved, fml_arena, tree_arena, entities);
            subproofs.push(tree);
            if !is_proved0 {
                // TODO: 2023/11/11 Unprovableとわかった時点で探索を終了すべきか
                is_proved = false;
            }
        }
        let tactic = Tactic { fml, seq_type };
        (Node { tactic, subproofs }, is_proved)
    } else {
        let cell = tree_arena.alloc(OnceCell::new());
        let tree = Unresolved(cell);
        unresolved.push((cell, seq));
        (tree, false)
    }
}

impl<'a> ProofTree<'a> {
    fn write_rec(
        &self,
        seqs: &mut Vec<(Sequent<'a>, bool)>,
        entities: &EntitiesInfo,
        output: OutputType,
        w: &mut BufWriter<impl Write>,
    ) -> Result<()> {
        use OutputType::*;
        use ProofTree::*;
        if matches!(output, Console) {
            for (seq, _) in seqs.iter().rev() {
                writeln!(w, "{}", &seq.display(entities))?;
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
                            seq.display(entities).to_latex()
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
                    writeln!(w, r"\hypo{{{}}}", seq.display(entities).to_latex())?;
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
                    proof.write_rec(seqs, entities, output, w)?;
                }
                if matches!(output, Latex) {
                    writeln!(
                        w,
                        r"\infer{{{len}}}[\scriptsize {label}]{{{}}}",
                        seq.display(entities).to_latex()
                    )?;
                }
            }
        }
        Ok(())
    }

    fn write(
        &self,
        fml: &'a Formula,
        entities: &EntitiesInfo,
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
        self.write_rec(&mut seqs, &entities, output, w)?;
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

    fn prove<'a>(
        &'a self,
        fml_arena: &'a Arena<Formula>,
        tree_arena: &'a Arena<OnceCell<ProofTree<'a>>>,
        entities: &mut EntitiesInfo,
    ) -> (ProofTree, bool) {
        let mut seqs = self.to_seqs();
        let mut seqs_waiting = vec![];
        let (tree, is_proved) = prove(
            &mut seqs,
            &mut seqs_waiting,
            fml_arena,
            tree_arena,
            entities,
        );
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

    pub fn assert_provable(&self, entities: &mut EntitiesInfo) {
        let fml_arena = Arena::new();
        let tree_arena = Arena::new();
        let (_, is_proved) = self.prove(&fml_arena, &tree_arena, entities);
        assert!(is_proved);
    }
}

pub fn example(s: &str) -> Result<()> {
    use crate::parser::parse;
    use std::time::Instant;

    // parse
    let (fml, mut entities) = parse(s).unwrap();
    let fml = fml.universal_quantify();
    println!("{}", fml.display(&entities));

    // prove
    let fml_arena = Arena::new();
    let tree_arena = Arena::new();
    let start_time = Instant::now();
    let (proof, is_proved) = fml.prove(&fml_arena, &tree_arena, &mut entities);
    let end_time = Instant::now();
    println!(">> {is_proved:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
    // assert!(is_proved);

    // print console
    let mut w = BufWriter::new(vec![]);
    proof.write(&fml, &entities, OutputType::Console, &mut w)?;
    println!("{}", String::from_utf8_lossy(&w.into_inner()?));

    // write latex
    let f = File::create("proof.tex")?;
    let mut w = BufWriter::new(f);
    proof.write(&fml, &entities, OutputType::Latex, &mut w)?;

    Ok(())
}

pub fn example_iltp_prop() {
    use crate::parser::from_tptp;
    use crate::parser::parse;
    use std::fs;
    use std::time::Instant;

    let s = fs::read_to_string("benches/iltp_prop/exclude.txt").unwrap();
    let exclude_list = s.lines().collect::<Vec<_>>();

    let files = fs::read_dir("benches/iltp_prop")
        .unwrap()
        .map(|entry| entry.unwrap().path());

    for file in files {
        let file_name = file.file_name().unwrap().to_str().unwrap();
        if exclude_list.contains(&file_name) {
            continue;
        }
        println!();
        println!("{file_name}");
        let s = fs::read_to_string(&file).unwrap();
        let (fml, mut entities) = parse(&from_tptp(&s)).unwrap();
        // println!("{}", fml.display(&entities));
        let fml_arena = Arena::new();
        let tree_arena = Arena::new();
        let start_time = Instant::now();
        let (_, is_proved) = fml.prove(&fml_arena, &tree_arena, &mut entities);
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
        let (fml, mut entities) = parse(s).unwrap();
        let fml = fml.universal_quantify();
        // prove
        let fml_arena = Arena::new();
        let tree_arena = Arena::new();
        let (proof, _) = fml.prove(&fml_arena, &tree_arena, &mut entities);
        // latex
        let mut w = BufWriter::new(vec![]);
        proof
            .write(&fml, &entities, OutputType::Latex, &mut w)
            .unwrap();
        String::from_utf8(w.into_inner().unwrap()).unwrap()
    }
}
