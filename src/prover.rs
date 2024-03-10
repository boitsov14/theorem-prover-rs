use crate::formula::{Formula, Term};
use crate::naming::{EntitiesInfo, Latex};
use crate::unification::{UnificationFailure, Unifier};
use core::hash::BuildHasherDefault;
use indexmap::IndexSet;
use itertools::{repeat_n, Itertools};
use maplit::{hashmap, hashset};
use rustc_hash::FxHasher;
use std::cell::OnceCell;
use std::collections::HashSet;
use std::fs::File;
use std::io::{self, BufWriter, Write};
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
enum FormulaPos {
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
    fml_pos: FormulaPos,
}

#[derive(Clone, Copy, Debug)]
enum OutputType {
    Console,
    Latex,
}

impl<'a> Sequent<'a> {
    fn get_fml(&self) -> Option<(&'a Formula, FormulaPos)> {
        use Formula::*;
        use FormulaPos::*;
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
        fml_pos: FormulaPos,
        seqs: &mut Vec<(Sequent<'a>, bool)>,
        fml_arena: &'a Arena<Formula>,
        new_id: &mut usize,
        free_vars: &Vec<usize>,
    ) -> usize {
        use Formula::*;
        use FormulaPos::*;
        match fml_pos {
            Ant => match fml {
                Not(p) => {
                    self.ant.swap_remove(fml);
                    self.suc.insert(p);
                    let is_proved = self.ant.contains(&**p);
                    seqs.push((self, is_proved));
                    1
                }
                And(l) => {
                    self.ant.swap_remove(fml);
                    for p in l {
                        self.ant.insert(p);
                    }
                    let is_proved = l.iter().any(|p| self.suc.contains(p));
                    seqs.push((self, is_proved));
                    1
                }
                Or(l) => {
                    self.ant.swap_remove(fml);
                    // TODO: 2024/02/29 読みやすさ改善要
                    for (p, mut seq) in l.iter().rev().zip(repeat_n(self, l.len())) {
                        seq.ant.insert(p);
                        let is_proved = seq.suc.contains(p);
                        seqs.push((seq, is_proved));
                    }
                    l.len()
                }
                Implies(p, q) => {
                    self.ant.swap_remove(fml);
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
                    self.ant.swap_remove(fml);
                    let p = fml_arena.alloc(*p.clone());
                    for v in vs {
                        // TODO: 2024/02/29 要改善
                        let free_vars = free_vars.iter().map(|v| Term::Var(*v)).collect();
                        let skolem_term = Term::Func(*new_id, free_vars);
                        *new_id += 1;
                        p.subst(*v, &skolem_term);
                    }
                    self.ant.insert(p);
                    seqs.push((self, false));
                    1
                }
                All(..) => unimplemented!(),
                Predicate(..) => unreachable!(),
            },
            Suc => match fml {
                Not(p) => {
                    self.suc.swap_remove(fml);
                    self.ant.insert(p);
                    let is_proved = self.suc.contains(&**p);
                    seqs.push((self, is_proved));
                    1
                }
                And(l) => {
                    // TODO: 2023/11/11 trueの場合
                    self.suc.swap_remove(fml);
                    for (p, mut seq) in l.iter().rev().zip(repeat_n(self, l.len())) {
                        seq.suc.insert(p);
                        let is_proved = seq.ant.contains(p);
                        seqs.push((seq, is_proved));
                    }
                    l.len()
                }
                Or(l) => {
                    self.suc.swap_remove(fml);
                    for p in l {
                        self.suc.insert(p);
                    }
                    let is_proved = l.iter().any(|p| self.ant.contains(p));
                    seqs.push((self, is_proved));
                    1
                }
                Implies(p, q) => {
                    self.suc.swap_remove(fml);
                    self.ant.insert(p);
                    self.suc.insert(q);
                    let is_proved = self.suc.contains(&**p) || self.ant.contains(&**q);
                    seqs.push((self, is_proved));
                    1
                }
                All(vs, p) => {
                    self.suc.swap_remove(fml);
                    let p = fml_arena.alloc(*p.clone());
                    for v in vs {
                        let free_vars = free_vars.iter().map(|v| Term::Var(*v)).collect();
                        let skolem_term = Term::Func(*new_id, free_vars);
                        *new_id += 1;
                        p.subst(*v, &skolem_term);
                    }
                    self.suc.insert(p);
                    seqs.push((self, false));
                    1
                }
                Exists(..) => unimplemented!(),
                Predicate(..) => unreachable!(),
            },
        }
    }

    fn prove_rec(
        self,
        seqs: &mut Vec<(Sequent<'a>, bool)>,
        unresolved: &mut Vec<(
            &'a OnceCell<ProofTree<'a>>,
            Sequent<'a>,
            HashSet<&'a Formula>,
        )>,
        fml_arena: &'a Arena<Formula>,
        tree_arena: &'a Arena<OnceCell<ProofTree<'a>>>,
        new_id: &mut usize,
        free_vars: &mut Vec<usize>,
    ) -> (ProofTree<'a>, bool) {
        use ProofTree::*;
        if let Some((fml, fml_pos)) = self.get_fml() {
            let len = self.apply_tactic(fml, fml_pos, seqs, fml_arena, new_id, free_vars);
            let mut subproofs = Vec::with_capacity(len);
            let mut is_proved = true;
            // TODO: 2023/11/30 for文で書くか，iterを使うか
            for _ in 0..len {
                let (seq, is_proved0) = seqs.pop().unwrap();
                if is_proved0 {
                    subproofs.push(Proved);
                    continue;
                }
                let (tree, is_proved0) =
                    seq.prove_rec(seqs, unresolved, fml_arena, tree_arena, new_id, free_vars);
                subproofs.push(tree);
                if !is_proved0 {
                    // TODO: 2023/11/11 Unprovableとわかった時点で探索を終了すべきか
                    is_proved = false;
                }
            }
            let tactic = Tactic { fml, fml_pos };
            (Node { tactic, subproofs }, is_proved)
        } else {
            let cell = tree_arena.alloc(OnceCell::new());
            let tree = Unresolved(cell);
            unresolved.push((cell, self, hashset!()));
            (tree, false)
        }
    }
}

impl<'a> ProofTree<'a> {
    fn write_rec(
        &self,
        seqs: &mut Vec<(Sequent<'a>, bool)>,
        fml_arena: &'a Arena<Formula>,
        new_id: &mut usize,
        entities: &EntitiesInfo,
        output: OutputType,
        w: &mut BufWriter<impl Write>,
    ) -> io::Result<()> {
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
                let Tactic { fml, fml_pos } = tactic;
                let len = seq
                    .clone()
                    .apply_tactic(fml, *fml_pos, seqs, fml_arena, new_id, &vec![]);
                assert_eq!(len, subproofs.len());
                let label = get_label(fml, fml_pos, output);
                if matches!(output, Console) {
                    writeln!(w, "{label}")?;
                }
                for proof in subproofs {
                    proof.write_rec(seqs, fml_arena, new_id, entities, output, w)?;
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
        fml_arena: &'a Arena<Formula>,
        entities: &EntitiesInfo,
        output: OutputType,
        w: &mut BufWriter<impl Write>,
    ) -> io::Result<()> {
        use OutputType::*;
        if matches!(output, Latex) {
            writeln!(
                w,
                r"\documentclass[preview,varwidth=\maxdimen,border=10pt]{{standalone}}"
            )?;
            writeln!(w, r"\usepackage{{ebproof}}")?;
            writeln!(w, r"\begin{{document}}")?;
            writeln!(w, r"\begin{{prooftree}}")?;
        }
        let mut seqs = vec![(fml.to_seq(), false)];
        self.write_rec(
            &mut seqs,
            fml_arena,
            &mut entities.len(),
            &entities,
            output,
            w,
        )?;
        assert!(seqs.is_empty());
        if matches!(output, Latex) {
            writeln!(w, r"\end{{prooftree}}")?;
            writeln!(w, r"\end{{document}}")?;
        }
        Ok(())
    }
}

fn get_label(fml: &Formula, fml_pos: &FormulaPos, output: OutputType) -> String {
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
    let fml_pos = match fml_pos {
        FormulaPos::Ant => ": Left",
        FormulaPos::Suc => ": Right",
    };
    format!("{fml_type}{fml_pos}")
}

impl Formula {
    fn to_seq(&self) -> Sequent {
        let mut seq = Sequent::default();
        seq.suc.insert(self);
        seq
    }

    fn prove<'a>(
        &'a self,
        fml_arena: &'a Arena<Formula>,
        tree_arena: &'a Arena<OnceCell<ProofTree<'a>>>,
        new_id: usize,
    ) -> (ProofTree, bool) {
        let mut new_id = new_id;
        let mut unresolved = vec![];
        let mut free_vars = vec![];
        let (tree, is_proved) = self.to_seq().prove_rec(
            &mut vec![],
            &mut unresolved,
            fml_arena,
            tree_arena,
            &mut new_id,
            &mut free_vars,
        );
        if is_proved {
            return (tree, true);
        }

        let mut unification_cnt = 0;
        const MAX_UNIFICATION_CNT: usize = 4;

        loop {
            'outer: loop {
                let Some((cell, seq, mut applied_fmls)) = unresolved.pop() else {
                    unreachable!();
                };

                // try apply ∀-left and ∃-right from unresolved sequents
                for fml in &seq.ant {
                    if let Formula::All(vs, p) = fml {
                        if applied_fmls.contains(fml) {
                            continue;
                        }
                        applied_fmls.insert(fml);
                        let p = fml_arena.alloc(*p.clone());
                        for v in vs {
                            p.subst(*v, &Term::Var(new_id));
                            free_vars.push(new_id);
                            new_id += 1;
                        }
                        let mut seq = seq.clone();
                        seq.ant.insert(p);
                        let mut new_unresolved = vec![];
                        let (sub_tree, is_proved) = seq.prove_rec(
                            &mut vec![],
                            &mut new_unresolved,
                            fml_arena,
                            tree_arena,
                            &mut new_id,
                            &mut free_vars,
                        );
                        for (_, _, new_applied_fmls) in new_unresolved.iter_mut() {
                            new_applied_fmls.extend(&applied_fmls);
                        }
                        unresolved.extend(new_unresolved);
                        cell.set(sub_tree).unwrap();
                        if is_proved {
                            return (tree, is_proved);
                        }
                        break 'outer;
                    }
                }

                for fml in &seq.suc {
                    if let Formula::Exists(vs, p) = fml {
                        // TODO: 2024/03/08 implement
                        break 'outer;
                    }
                }

                // When there are no ∀-lefts nor ∃-rights
                if applied_fmls.is_empty() {
                    return (tree, false);
                }

                // When there are ∀-lefts or ∃-rights, but all of them are already applied
                // check unification count
                if unification_cnt >= MAX_UNIFICATION_CNT {
                    // TODO: 2024/03/10 falseではなくfailure
                    return (tree, false);
                }
                applied_fmls.clear();
                unification_cnt += 1;
                unresolved.push((cell, seq, applied_fmls));
            }

            // try unify unresolved sequents
            let mut pair_matrix = Vec::with_capacity(unresolved.len());
            for (_, seq, _) in &unresolved {
                let mut pairs = vec![];
                for p in &seq.ant {
                    if let Formula::Predicate(id1, terms1) = p {
                        for q in &seq.suc {
                            if let Formula::Predicate(id2, terms2) = q {
                                if id1 == id2 && terms1.len() == terms2.len() {
                                    let pair = (terms1, terms2);
                                    pairs.push(pair);
                                }
                            };
                        }
                    };
                }
                pair_matrix.push(pairs);
            }

            fn unify_pairs_matrix(
                pair_matrix: &[Vec<(&Vec<Term>, &Vec<Term>)>],
                u: &mut Unifier,
            ) -> Result<(), UnificationFailure> {
                if pair_matrix.is_empty() {
                    return Ok(());
                }
                let pairs = &pair_matrix[0];
                for pair in pairs {
                    let (terms1, terms2) = pair;
                    for (t1, t2) in terms1.iter().zip(terms2.iter()) {
                        match t1.unify(t2, u) {
                            Ok(_) => match unify_pairs_matrix(&pair_matrix[1..], u) {
                                Ok(_) => return Ok(()),
                                Err(_) => {}
                            },
                            Err(_) => {}
                        }
                    }
                }
                Err(UnificationFailure)
            }

            // TODO: 2024/03/10 uは引数にする
            let mut u = hashmap!();
            match unify_pairs_matrix(&pair_matrix, &mut u) {
                Ok(_) => {
                    return (tree, true);
                }
                Err(_) => {
                    continue;
                }
            }
        }
    }

    pub fn assert_provable(&self, new_id: usize) {
        let fml_arena = Arena::new();
        let tree_arena = Arena::new();
        let (_, is_proved) = self.prove(&fml_arena, &tree_arena, new_id);
        assert!(is_proved);
    }
}

pub fn example(s: &str) -> io::Result<()> {
    use crate::parser::parse;
    use std::time::Instant;

    // parse
    let (fml, entities) = parse(s).unwrap();
    let fml = fml.universal_quantify();
    println!("{}", fml.display(&entities));

    // prove
    let fml_arena = Arena::new();
    let tree_arena = Arena::new();
    let start_time = Instant::now();
    let (proof, is_proved) = fml.prove(&fml_arena, &tree_arena, entities.len());
    let end_time = Instant::now();
    println!(">> {is_proved:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
    // assert!(is_proved);

    // print console
    let mut w = BufWriter::new(vec![]);
    proof.write(&fml, &fml_arena, &entities, OutputType::Console, &mut w)?;
    println!("{}", String::from_utf8_lossy(&w.into_inner()?));

    // write latex
    let f = File::create("proof.tex")?;
    let mut w = BufWriter::new(f);
    proof.write(&fml, &fml_arena, &entities, OutputType::Latex, &mut w)?;

    Ok(())
}

pub fn example_iltp_prop() {
    use crate::parser::from_tptp;
    use crate::parser::parse;
    use std::fs;
    use std::time::Instant;

    let s = fs::read_to_string("benches/iltp_prop/exclude.txt").unwrap();
    let exclude_list = s.lines().collect_vec();

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
        let (fml, entities) = parse(&from_tptp(&s)).unwrap();
        // println!("{}", fml.display(&entities));
        let fml_arena = Arena::new();
        let tree_arena = Arena::new();
        let start_time = Instant::now();
        let (_, is_proved) = fml.prove(&fml_arena, &tree_arena, entities.len());
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
        let (fml, entities) = parse(s).unwrap();
        let fml = fml.universal_quantify();
        // prove
        let fml_arena = Arena::new();
        let tree_arena = Arena::new();
        let (proof, _) = fml.prove(&fml_arena, &tree_arena, entities.len());
        // latex
        let mut w = BufWriter::new(vec![]);
        proof
            .write(&fml, &fml_arena, &entities, OutputType::Latex, &mut w)
            .unwrap();
        String::from_utf8(w.into_inner().unwrap()).unwrap()
    }
}
