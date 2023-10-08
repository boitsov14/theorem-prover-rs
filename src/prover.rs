use std::collections::HashSet;

use crate::formula::{All, And, Exists, Formula, Iff, Implies, Not, Or, Predicate, FALSE, TRUE};

/// Structured set of formulae
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Formulae {
    predicate_set: HashSet<Predicate>,
    not_set: HashSet<Not>,
    and_set: HashSet<And>,
    or_set: HashSet<Or>,
    implies_set: HashSet<Implies>,
    iff_set: HashSet<Iff>,
    all_set: HashSet<All>,
    exists_set: HashSet<Exists>,
}

/// Sequent of structured formulae
#[derive(Clone, Debug, Eq, PartialEq)]
struct Sequent {
    antecedent: Formulae,
    succedent: Formulae,
}

/// Sequent of formulae
#[derive(Clone, Debug, Eq, PartialEq)]
struct PlainSequent {
    antecedent: HashSet<Formula>,
    succedent: HashSet<Formula>,
}

#[derive(Debug)]
enum AxiomTactic {
    Axiom,
    LFalse,
    RTrue,
}

#[derive(Debug)]
enum UnaryTactic {
    LNot,
    RNot,
    LAnd,
    ROr,
    RImplies,
    LIff,
}

#[derive(Debug)]
enum BinaryTactic {
    LImplies,
    RIff,
}

enum NaryTactic {
    RAnd,
    LOr,
}

impl Sequent {
    fn new(antecedent: Formulae, succedent: Formulae) -> Self {
        Self {
            antecedent,
            succedent,
        }
    }
    fn to_axiom(&self) -> Option<AxiomTactic> {
        use AxiomTactic::*;
        if self
            .antecedent
            .predicate_set
            .intersection(&self.succedent.predicate_set)
            .next()
            .is_some()
        {
            Some(Axiom)
        } else if self.antecedent.or_set.contains(&FALSE) {
            Some(LFalse)
        } else if self.succedent.and_set.contains(&TRUE) {
            Some(RTrue)
        } else {
            None
        }
    }
}
