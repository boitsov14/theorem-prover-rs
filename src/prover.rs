use indexmap::IndexSet;

use crate::formula::{All, And, Exists, Formula, Implies, Not, Or, Predicate};

use itertools::repeat_n;

/// Structured set of formulae
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Formulae {
    predicate_set: IndexSet<Predicate>,
    not_set: IndexSet<Not>,
    and_set: IndexSet<And>,
    or_set: IndexSet<Or>,
    implies_set: IndexSet<Implies>,
    all_set: IndexSet<All>,
    exists_set: IndexSet<Exists>,
}

/// Sequent of structured formulae
#[derive(Clone, Debug, Eq, PartialEq)]
struct Sequent {
    ant: Formulae,
    suc: Formulae,
}

/// Sequent of formulae
#[derive(Clone, Debug, Eq, PartialEq)]
struct PlainSequent {
    ant: IndexSet<Formula>,
    suc: IndexSet<Formula>,
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
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

struct ProofTree {
    tactic: Tactic,
    subproofs: Vec<ProofTree>,
}

enum ProofState {
    Provable,
    InProgress,
    UnProvable,
}

impl Sequent {
    fn new(ant: Formulae, suc: Formulae) -> Self {
        Self { ant, suc }
    }
    fn insert_to_ant(&mut self, fml: Formula) -> ProofState {
        use ProofState::*;
        match fml {
            Formula::Predicate(id, terms) => {
                let p = Predicate(id, terms);
                if self.suc.predicate_set.contains(&p) {
                    self.ant.predicate_set.insert(p);
                    return Provable;
                }
                self.ant.predicate_set.insert(p);
            }
            Formula::Not(p) => {
                self.ant.not_set.insert(Not(p));
            }
            Formula::And(l) => {
                self.ant.and_set.insert(And(l));
            }
            Formula::Or(l) => {
                // TODO: 2023/10/10 pがF_FALSEかどうかの判定をする？
                self.ant.or_set.insert(Or(l));
            }
            Formula::Implies(p, q) => {
                self.ant.implies_set.insert(Implies(p, q));
            }
            Formula::All(vs, p) => {
                self.ant.all_set.insert(All(vs, p));
            }
            Formula::Exists(vs, p) => {
                self.ant.exists_set.insert(Exists(vs, p));
            }
        }
        InProgress
    }
    fn insert_to_suc(&mut self, fml: Formula) -> ProofState {
        use ProofState::*;
        match fml {
            Formula::Predicate(id, terms) => {
                let p = Predicate(id, terms);
                if self.ant.predicate_set.contains(&p) {
                    self.suc.predicate_set.insert(p);
                    return Provable;
                }
                self.suc.predicate_set.insert(p);
            }
            Formula::Not(p) => {
                self.suc.not_set.insert(Not(p));
            }
            Formula::And(l) => {
                self.suc.and_set.insert(And(l));
            }
            Formula::Or(l) => {
                self.suc.or_set.insert(Or(l));
            }
            Formula::Implies(p, q) => {
                self.suc.implies_set.insert(Implies(p, q));
            }
            Formula::All(vs, p) => {
                self.suc.all_set.insert(All(vs, p));
            }
            Formula::Exists(vs, p) => {
                self.suc.exists_set.insert(Exists(vs, p));
            }
        }
        InProgress
    }
}

struct TacticResult {
    tactic: Tactic,
    sequents: Vec<(Sequent, ProofState)>,
}

impl TacticResult {
    fn new(tactic: Tactic, sequents: Vec<(Sequent, ProofState)>) -> Self {
        Self { tactic, sequents }
    }
}

impl Tactic {
    fn apply(self, mut sequent: Sequent) -> Option<TacticResult> {
        use Tactic::*;
        match self {
            LNot => {
                let Not(p) = sequent.ant.not_set.pop()?;
                let state = sequent.insert_to_suc(*p);
                Some(TacticResult::new(self, vec![(sequent, state)]))
            }
            RNot => {
                let Not(p) = sequent.suc.not_set.pop()?;
                let state = sequent.insert_to_ant(*p);
                Some(TacticResult::new(self, vec![(sequent, state)]))
            }
            RImplies => {
                let Implies(p, q) = sequent.suc.implies_set.pop()?;
                let mut sequent_l = sequent.clone();
                let mut sequent_r = sequent;
                let state_l = sequent_l.insert_to_ant(*p);
                let state_r = sequent_r.insert_to_suc(*q);
                Some(TacticResult::new(
                    self,
                    vec![(sequent_l, state_l), (sequent_r, state_r)],
                ))
            }
            LAnd => {
                let And(l) = sequent.ant.and_set.pop()?;
                let mut state = ProofState::InProgress;
                for p in l {
                    if let ProofState::Provable = sequent.insert_to_ant(p) {
                        state = ProofState::Provable;
                    }
                }
                Some(TacticResult::new(self, vec![(sequent, state)]))
            }
            ROr => todo!(),
            LImplies => todo!(),
            RAnd => {
                let And(l) = sequent.suc.and_set.pop()?;
                let n = l.len();
                let l = l.into_iter().zip(repeat_n(sequent, n));
                let mut sequents = Vec::with_capacity(n);
                for (p, mut sequent) in l {
                    let state = sequent.insert_to_suc(p);
                    sequents.push((sequent, state));
                }
                Some(TacticResult::new(self, sequents))
            }
            LOr => {
                let Or(l) = sequent.ant.or_set.pop()?;
                let n = l.len();
                let l = l.into_iter().zip(repeat_n(sequent, n));
                let mut sequents = Vec::with_capacity(n);
                for (p, mut sequent) in l {
                    let state = sequent.insert_to_ant(p);
                    sequents.push((sequent, state));
                }
                Some(TacticResult::new(self, sequents))
            }
        }
    }
}
