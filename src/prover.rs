use std::collections::HashSet;

use crate::formula::{All, And, Exists, Formula, Iff, Implies, NamingInfo, Not, Or, Predicate};

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

#[derive(Clone, Debug, Eq, PartialEq)]
struct Sequent {
    antecedent: Formulae,
    succedent: Formulae,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PlainSequent {
    antecedent: HashSet<Formula>,
    succedent: HashSet<Formula>,
}

impl Sequent {
    fn new(antecedent: Formulae, succedent: Formulae) -> Self {
        Self {
            antecedent,
            succedent,
        }
    }
}
