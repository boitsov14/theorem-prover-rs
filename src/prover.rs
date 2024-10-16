use crate::lang::{Formula, Formula::*, Sequent as RawSequent, Term};
use crate::name::Names;
use crate::parser::parse_sequent;
use crate::unification::{resolve_unifier, UnificationFailure, Unifier};
use core::hash::BuildHasherDefault;
use indexmap::IndexSet;
use itertools::{repeat_n, Itertools};
use maplit::{hashmap, hashset};
use rustc_hash::FxHasher;
use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufWriter, Write};
use typed_arena::Arena;

const MAX_UNIFICATION_CNT: usize = 100;

type FxIndexSet<T> = IndexSet<T, BuildHasherDefault<FxHasher>>;

/// Sequent of formulae
#[derive(Clone, Debug, Default)]
pub(super) struct Sequent<'a> {
    ant: FxIndexSet<&'a Formula>,
    suc: FxIndexSet<&'a Formula>,
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
enum ProofResult {
    Provable,
    Unprovable,
    Failure,
}

#[derive(Clone, Copy, Debug)]
enum OutputType {
    Console,
    Latex,
}

impl<'a> Sequent<'a> {
    fn into_raw(self) -> RawSequent<'a> {
        let ant = self.ant.into_iter().collect();
        let suc = self.suc.into_iter().collect();
        RawSequent { ant, suc }
    }
    fn get_fml(&self) -> Option<(&'a Formula, FormulaPos)> {
        for fml in &self.ant {
            match fml {
                Not(_) | And(_) | Ex(..) => {
                    return Some((fml, FormulaPos::Ant));
                }
                _ => {}
            }
        }
        for fml in &self.suc {
            match fml {
                Not(_) | Or(_) | To(..) | All(..) => {
                    return Some((fml, FormulaPos::Suc));
                }
                _ => {}
            }
        }
        for fml in &self.ant {
            match fml {
                Or(l) => {
                    if l.iter().all(|p| !self.ant.contains(p)) {
                        return Some((fml, FormulaPos::Ant));
                    }
                }
                To(p, q) => {
                    if !self.suc.contains(&**p) && !self.ant.contains(&**q) {
                        return Some((fml, FormulaPos::Ant));
                    }
                }
                _ => {}
            }
        }
        for fml in &self.suc {
            if let And(l) = fml {
                if l.iter().all(|p| !self.suc.contains(p)) {
                    return Some((fml, FormulaPos::Suc));
                }
            }
        }
        None
    }

    fn apply_tactic(
        mut self,
        fml: &'a Formula,
        fml_pos: FormulaPos,
        seqs: &mut Vec<(Self, bool)>,
        fml_arena: &'a Arena<Formula>,
        new_id: &mut usize,
        free_vars: &mut Vec<usize>,
    ) -> usize {
        match fml_pos {
            FormulaPos::Ant => match fml {
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
                To(p, q) => {
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
                Iff(p, q) => {
                    todo!()
                }
                Ex(vs, p) => {
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
                All(vs, p) => {
                    let p = fml_arena.alloc(*p.clone());
                    for v in vs {
                        p.subst(*v, &Term::Var(*new_id));
                        free_vars.push(*new_id);
                        *new_id += 1;
                    }
                    self.ant.insert(p);
                    seqs.push((self, false));
                    1
                }
                Pred(..) => unreachable!(),
            },
            FormulaPos::Suc => match fml {
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
                To(p, q) => {
                    self.suc.swap_remove(fml);
                    self.ant.insert(p);
                    self.suc.insert(q);
                    let is_proved = self.suc.contains(&**p) || self.ant.contains(&**q);
                    seqs.push((self, is_proved));
                    1
                }
                Iff(p, q) => {
                    todo!()
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
                Ex(vs, p) => {
                    let p = fml_arena.alloc(*p.clone());
                    for v in vs {
                        p.subst(*v, &Term::Var(*new_id));
                        free_vars.push(*new_id);
                        *new_id += 1;
                    }
                    self.suc.insert(p);
                    seqs.push((self, false));
                    1
                }
                Pred(..) => unreachable!(),
            },
        }
    }

    fn prove_rec(
        self,
        seqs: &mut Vec<(Self, bool)>,
        unresolved: &mut Vec<(&'a OnceCell<ProofTree<'a>>, Self, HashSet<&'a Formula>)>,
        fml_arena: &'a Arena<Formula>,
        tree_arena: &'a Arena<OnceCell<ProofTree<'a>>>,
        new_id: &mut usize,
        free_vars: &mut Vec<usize>,
    ) -> ProofTree<'a> {
        if let Some((fml, fml_pos)) = self.get_fml() {
            let len = self.apply_tactic(fml, fml_pos, seqs, fml_arena, new_id, free_vars);
            let mut subproofs = Vec::with_capacity(len);
            for _ in 0..len {
                let (seq, is_proved) = seqs.pop().unwrap();
                if is_proved {
                    subproofs.push(ProofTree::Proved);
                    continue;
                }
                let tree =
                    seq.prove_rec(seqs, unresolved, fml_arena, tree_arena, new_id, free_vars);
                subproofs.push(tree);
            }
            let tactic = Tactic { fml, fml_pos };
            ProofTree::Node { tactic, subproofs }
        } else {
            let cell = tree_arena.alloc(OnceCell::new());
            let tree = ProofTree::Unresolved(cell);
            unresolved.push((cell, self, hashset!()));
            tree
        }
    }

    fn format_for_print(
        self,
        u: &HashMap<usize, Term>,
        skolem_ids: &HashSet<usize>,
        fml_arena: &'a Arena<Formula>,
    ) -> Self {
        let mut ant: IndexSet<&Formula, _> = FxIndexSet::default();
        let mut suc: IndexSet<&Formula, _> = FxIndexSet::default();
        for fml in self.ant {
            let mut fml = fml.clone();
            fml.subst_map(u);
            for id in skolem_ids {
                fml.replace_func_with_var(*id);
            }
            ant.insert(fml_arena.alloc(fml));
        }
        for fml in self.suc {
            let mut fml = fml.clone();
            fml.subst_map(u);
            for id in skolem_ids {
                fml.replace_func_with_var(*id);
            }
            suc.insert(fml_arena.alloc(fml));
        }
        Sequent { ant, suc }
    }
}

impl<'a> ProofTree<'a> {
    fn write_rec(
        &self,
        seqs: &mut Vec<(Sequent<'a>, bool)>,
        fml_arena: &'a Arena<Formula>,
        new_id: &mut usize,
        names: &Names,
        skolem_ids: &HashSet<usize>,
        u: &HashMap<usize, Term>,
        output: OutputType,
        w: &mut BufWriter<impl Write>,
    ) -> io::Result<()> {
        if matches!(output, OutputType::Console) {
            for (seq, _) in seqs.iter().rev() {
                writeln!(
                    w,
                    "{}",
                    &seq.clone()
                        .format_for_print(u, skolem_ids, fml_arena)
                        .into_raw()
                        .display(names)
                )?;
            }
        }
        let (seq, _) = seqs.pop().unwrap();
        match self {
            ProofTree::Proved => {
                // TODO: 2024/03/14 unificationを考慮する
                // assert!(!seq.ant.is_disjoint(&seq.suc));
                match output {
                    OutputType::Console => {
                        writeln!(w, "Axiom")?;
                    }
                    OutputType::Latex => {
                        writeln!(
                            w,
                            r"\infer{{0}}[\scriptsize Axiom]{{{}}}",
                            seq.format_for_print(u, skolem_ids, fml_arena)
                                .into_raw()
                                .display(names)
                                .to_latex()
                        )?;
                    }
                }
            }
            // TODO: 2023/12/02 Unresolvedがあとから解決された場合の処理
            ProofTree::Unresolved(cell) => match cell.get() {
                Some(tree) => {
                    seqs.push((seq, false));
                    tree.write_rec(seqs, fml_arena, new_id, names, skolem_ids, u, output, w)?;
                }
                None => match output {
                    OutputType::Console => {
                        writeln!(w, "UnProvable")?;
                    }
                    OutputType::Latex => {
                        writeln!(
                            w,
                            r"\hypo{{{}}}",
                            seq.format_for_print(u, skolem_ids, fml_arena)
                                .into_raw()
                                .display(names)
                                .to_latex()
                        )?;
                    }
                },
            },
            ProofTree::Node { tactic, subproofs } => {
                let Tactic { fml, fml_pos } = tactic;
                let len =
                    seq.clone()
                        .apply_tactic(fml, *fml_pos, seqs, fml_arena, new_id, &mut vec![]);
                assert_eq!(len, subproofs.len());
                let label = get_label(fml, *fml_pos, output);
                if matches!(output, OutputType::Console) {
                    writeln!(w, "{label}")?;
                }
                for proof in subproofs {
                    proof.write_rec(seqs, fml_arena, new_id, names, skolem_ids, u, output, w)?;
                }
                if matches!(output, OutputType::Latex) {
                    writeln!(
                        w,
                        r"\infer{{{len}}}[\scriptsize {label}]{{{}}}",
                        seq.format_for_print(u, skolem_ids, fml_arena)
                            .into_raw()
                            .display(names)
                            .to_latex()
                    )?;
                }
            }
        }
        Ok(())
    }

    fn write(
        &self,
        seq: Sequent<'a>,
        fml_arena: &'a Arena<Formula>,
        names: &Names,
        new_id: usize,
        skolem_ids: &HashSet<usize>,
        u: &HashMap<usize, Term>,
        output: OutputType,
        w: &mut BufWriter<impl Write>,
    ) -> io::Result<()> {
        if matches!(output, OutputType::Latex) {
            writeln!(
                w,
                r"\documentclass[preview,varwidth=\maxdimen,border=10pt]{{standalone}}"
            )?;
            writeln!(w, r"\usepackage{{ebproof}}")?;
            writeln!(w, r"\begin{{document}}")?;
            writeln!(w, r"\begin{{prooftree}}")?;
        }
        let mut seqs = vec![(seq, false)];
        self.write_rec(
            &mut seqs,
            fml_arena,
            &mut new_id.clone(),
            names,
            skolem_ids,
            u,
            output,
            w,
        )?;
        assert!(seqs.is_empty());
        if matches!(output, OutputType::Latex) {
            writeln!(w, r"\end{{prooftree}}")?;
            writeln!(w, r"\end{{document}}")?;
        }
        Ok(())
    }
}

fn get_label(fml: &Formula, fml_pos: FormulaPos, output: OutputType) -> String {
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
            [To(p_l, q_l), To(p_r, q_r)] if p_l == q_r && q_l == p_r => match output {
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
        To(..) => match output {
            Console => "→",
            Latex => r"$\rightarrow$",
        },
        Iff(..) => match output {
            Console => "↔",
            Latex => r"$\leftrightarrow$",
        },
        All(..) => match output {
            Console => "∀",
            Latex => r"$\forall$",
        },
        Ex(..) => match output {
            Console => "∃",
            Latex => r"$\exists$",
        },
        Pred(..) => unreachable!(),
    };
    let fml_pos = match fml_pos {
        FormulaPos::Ant => ": Left",
        FormulaPos::Suc => ": Right",
    };
    format!("{fml_type}{fml_pos}")
}

impl Term {
    /// Replaces a function with a variable of the same ID.
    fn replace_func_with_var(&mut self, id: usize) {
        self.visit_mut(&mut |f| {
            let Self::Func(f_id, _) = f else { return };
            if *f_id == id {
                *f = Self::Var(id);
            }
        });
    }
}

impl Formula {
    // TODO: 2024/05/13 apply_mutを使う
    // TODO: 2024/04/06 引数をskolem_idsにする
    pub(super) fn replace_func_with_var(&mut self, id: usize) {
        use Formula::*;
        match self {
            Pred(_, ts) => {
                for t in ts {
                    t.replace_func_with_var(id);
                }
            }
            Not(p) => p.replace_func_with_var(id),
            And(l) | Or(l) => {
                for p in l {
                    p.replace_func_with_var(id);
                }
            }
            To(p, q) | Iff(p, q) => {
                p.replace_func_with_var(id);
                q.replace_func_with_var(id);
            }
            All(_, p) | Ex(_, p) => {
                p.replace_func_with_var(id);
            }
        }
    }
}

impl<'a> RawSequent<'a> {
    fn to_seq(&self) -> Sequent {
        let mut seq = Sequent::default();
        for fml in &self.ant {
            seq.ant.insert(fml);
        }
        for fml in &self.suc {
            seq.suc.insert(fml);
        }
        seq
    }
}

impl<'a> Sequent<'a> {
    fn prove(
        self,
        fml_arena: &'a Arena<Formula>,
        tree_arena: &'a Arena<OnceCell<ProofTree<'a>>>,
        new_id: usize,
    ) -> (
        ProofTree<'a>,
        ProofResult,
        HashMap<usize, Term>,
        Vec<usize>,
        usize,
    ) {
        let mut unresolved = vec![];
        let mut free_vars = vec![];
        let mut new_id = new_id;
        let tree = self.prove_rec(
            &mut vec![],
            &mut unresolved,
            fml_arena,
            tree_arena,
            &mut new_id,
            &mut free_vars,
        );
        if unresolved.is_empty() {
            return (tree, ProofResult::Provable, hashmap!(), free_vars, new_id);
        }

        let mut unification_cnt = 0;

        loop {
            'outer: loop {
                // TODO: 2024/03/14 後で消す
                // println!("-----------------------------------------------");
                // for (_, seq, _) in &unresolved {
                //     println!("seq: {}", seq.display(&EntitiesInfo::default()));
                // }

                let Some((cell, seq, mut applied_fmls)) = unresolved.pop() else {
                    unreachable!();
                };

                // try to apply ∀-left
                let mut fml_all = None;
                for fml in &seq.ant {
                    if matches!(fml, All(..)) && !applied_fmls.contains(fml) {
                        fml_all = Some(*fml);
                    }
                }
                if let Some(fml) = fml_all {
                    applied_fmls.insert(fml);
                    let fml_pos = FormulaPos::Ant;
                    let mut seqs = vec![];
                    seq.apply_tactic(
                        fml,
                        fml_pos,
                        &mut seqs,
                        fml_arena,
                        &mut new_id,
                        &mut free_vars,
                    );
                    let (seq, _) = seqs.pop().unwrap();
                    let mut new_unresolved = vec![];
                    let sub_tree = seq.prove_rec(
                        &mut vec![],
                        &mut new_unresolved,
                        fml_arena,
                        tree_arena,
                        &mut new_id,
                        &mut free_vars,
                    );
                    for (_, _, new_applied_fmls) in &mut new_unresolved {
                        new_applied_fmls.extend(&applied_fmls);
                    }
                    unresolved.extend(new_unresolved);
                    let tactic = Tactic { fml, fml_pos };
                    cell.set(ProofTree::Node {
                        tactic,
                        subproofs: vec![sub_tree],
                    })
                    .unwrap();
                    break 'outer;
                }

                // try to apply ∃-right
                let mut fml_ex = None;
                for fml in &seq.suc {
                    if matches!(fml, Ex(..)) && !applied_fmls.contains(fml) {
                        fml_ex = Some(*fml);
                    }
                }
                if let Some(fml) = fml_ex {
                    applied_fmls.insert(fml);
                    let fml_pos = FormulaPos::Suc;
                    let mut seqs = vec![];
                    seq.apply_tactic(
                        fml,
                        fml_pos,
                        &mut seqs,
                        fml_arena,
                        &mut new_id,
                        &mut free_vars,
                    );
                    let (seq, _) = seqs.pop().unwrap();
                    let mut new_unresolved = vec![];
                    let sub_tree = seq.prove_rec(
                        &mut vec![],
                        &mut new_unresolved,
                        fml_arena,
                        tree_arena,
                        &mut new_id,
                        &mut free_vars,
                    );
                    for (_, _, new_applied_fmls) in &mut new_unresolved {
                        new_applied_fmls.extend(&applied_fmls);
                    }
                    unresolved.extend(new_unresolved);
                    let tactic = Tactic { fml, fml_pos };
                    let subproofs = vec![sub_tree];
                    cell.set(ProofTree::Node { tactic, subproofs }).unwrap();
                    break 'outer;
                }

                // When there are no ∀-lefts nor ∃-rights
                if applied_fmls.is_empty() {
                    return (tree, ProofResult::Unprovable, hashmap!(), free_vars, new_id);
                }

                // When there are ∀-lefts or ∃-rights, but all of them are already applied
                // check unification count
                if unification_cnt >= MAX_UNIFICATION_CNT {
                    // TODO: 2024/03/14 後で消す
                    println!("unification_cnt >= MAX_UNIFICATION_CNT");
                    return (tree, ProofResult::Failure, hashmap!(), free_vars, new_id);
                }
                applied_fmls.clear();
                unification_cnt += 1;
                unresolved.push((cell, seq, applied_fmls));
                // TODO: 2024/03/12 Kotlin版とcntの方法が異なる
                println!("unification_cnt: {unification_cnt}");
            }

            // try unify unresolved sequents
            let mut pair_matrix = Vec::with_capacity(unresolved.len());
            for (_, seq, _) in &unresolved {
                let mut pairs = vec![];
                for p in &seq.ant {
                    if let Pred(id1, terms1) = p {
                        'outer0: for q in &seq.suc {
                            if let Pred(id2, terms2) = q {
                                if id1 == id2 && terms1.len() == terms2.len() {
                                    let mut u = vec![];
                                    for (t1, t2) in terms1.iter().zip(terms2.iter()) {
                                        if t1.get_unifiable_pairs(t2, &mut u).is_err() {
                                            continue 'outer0;
                                        }
                                    }
                                    pairs.push(u);
                                }
                            };
                        }
                    };
                }
                pair_matrix.push(pairs);
            }

            // TODO: 2024/03/14 どうするか
            // pair_matrix.sort_by_key(|pairs| pairs.len());

            // TODO: 2024/03/14 後で消す
            // println!("pair_matrix");
            // for pairs in &pair_matrix {
            //     println!("pairs");
            //     for u in pairs {
            //         println!("  u: {:?}", u);
            //     }
            // }
            // println!("pair_matrix_end");

            let mut u = hashmap!();
            for v in &free_vars {
                u.insert(*v, OnceCell::new());
            }
            match unify_pairs_matrix(&pair_matrix, &mut u) {
                Ok(()) => {
                    for (cell, _, _) in &mut unresolved {
                        cell.set(ProofTree::Proved).unwrap();
                    }
                    return (
                        tree,
                        ProofResult::Provable,
                        resolve_unifier(&u),
                        free_vars,
                        new_id,
                    );
                }
                Err(_) => {
                    continue;
                }
            }
        }
    }

    fn assert_provable(self, new_id: usize) {
        let fml_arena = Arena::new();
        let tree_arena = Arena::new();
        let (_, result, _, _, _) = self.prove(&fml_arena, &tree_arena, new_id);
        assert!(matches!(result, ProofResult::Provable));
    }
}

fn unify_pairs_matrix(
    pair_matrix: &[Vec<Vec<(&Term, &Term)>>],
    u: &mut Unifier,
) -> Result<(), UnificationFailure> {
    let Some(pairs) = pair_matrix.first() else {
        return Ok(());
    };
    let old_u = u.clone();
    for pair in pairs {
        for (t1, t2) in pair {
            if t1.unify(t2, u).is_ok() {
                if unify_pairs_matrix(&pair_matrix[1..], u).is_ok() {
                    return Ok(());
                }
            } else {
                u.clone_from(&old_u);
            }
        }
    }
    Err(UnificationFailure)
}

pub fn example(s: &str) -> io::Result<()> {
    use crate::parser::parse_sequent;
    use std::time::Instant;

    // parse
    let mut names = Names::default();
    let seq = match parse_sequent(s, &mut names, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            println!("{e}");
            return Ok(());
        }
    };
    let seq = seq.to_seq();
    println!("{}", seq.display(&names));
    let seq = seq.to_seq();

    // prove
    let fml_arena = Arena::new();
    let tree_arena = Arena::new();
    let start_time = Instant::now();
    let (proof, result, u, free_vars, new_id) =
        seq.clone().prove(&fml_arena, &tree_arena, names.len());
    let end_time = Instant::now();
    println!("u: {u:?}");
    println!(">> {result:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);

    return Ok(());

    let old_id = names.len();
    let mut skolem_ids = hashset!();
    if matches!(result, ProofResult::Failure) {
        let mut variable_id = 0;
        let mut function_id = 0;
        for i in old_id..new_id {
            if free_vars.contains(&i) {
                names.get_id(format!("v_{variable_id}"));
                variable_id += 1;
            } else {
                names.get_id(format!("t_{function_id}"));
                function_id += 1;
            }
        }
    } else {
        let mut function_id = 0;
        for i in old_id..new_id {
            if !free_vars.contains(&i) {
                names.get_id(format!("v_{function_id}"));
                skolem_ids.insert(i);
                function_id += 1;
            }
        }
    }

    // print console
    let mut w = BufWriter::new(vec![]);
    proof.write(
        seq.clone(),
        &fml_arena,
        &names,
        old_id,
        &skolem_ids,
        &u,
        OutputType::Console,
        &mut w,
    )?;
    println!("{}", String::from_utf8_lossy(&w.into_inner()?));

    // write latex
    let f = File::create("proof.tex")?;
    let mut w = BufWriter::new(f);
    proof.write(
        seq,
        &fml_arena,
        &names,
        old_id,
        &skolem_ids,
        &u,
        OutputType::Latex,
        &mut w,
    )?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let mut names = Names::default();
        let seq = parse_sequent(s, &mut names, true, false).unwrap();
        let seq = seq.to_seq();
        // prove
        let fml_arena = Arena::new();
        let tree_arena = Arena::new();
        let (proof, _, u, free_vars, new_id) =
            seq.to_seq().prove(&fml_arena, &tree_arena, names.len());
        // latex
        let mut w = BufWriter::new(vec![]);
        proof
            .write(
                seq.to_seq(),
                &fml_arena,
                &names,
                names.len(),
                &hashset!(), // TODO: 2024/03/14
                &u,
                OutputType::Latex,
                &mut w,
            )
            .unwrap();
        String::from_utf8(w.into_inner().unwrap()).unwrap()
    }
}
