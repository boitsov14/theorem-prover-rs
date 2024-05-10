use maplit::hashset;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Term {
    Var(usize),
    Func(usize, Vec<Term>),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Formula {
    Pred(usize, Vec<Term>),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    All(Vec<usize>, Box<Formula>),
    Exists(Vec<usize>, Box<Formula>),
}

impl Term {
    /// Applies a function to the term and its subterms recursively.
    fn apply<F>(&self, f: &mut F)
    where
        F: FnMut(&Self),
    {
        f(self);
        if let Self::Func(_, terms) = self {
            for term in terms {
                term.apply(f);
            }
        }
    }

    /// Applies a function to the term and its subterms recursively, allowing mutation of the term.
    fn apply_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        f(self);
        if let Self::Func(_, terms) = self {
            for term in terms {
                term.apply_mut(f);
            }
        }
    }

    /// Collects function IDs in the term.
    fn collect_func(&self, ids: &mut HashSet<usize>) {
        self.apply(&mut |t| {
            if let Self::Func(id, _) = t {
                ids.insert(*id);
            }
        });
    }

    /// Substitutes a variable with a new term.
    fn subst(&mut self, var: usize, new_term: &Self) {
        self.apply_mut(&mut |v| {
            if let Self::Var(id) = v {
                if *id == var {
                    *v = new_term.clone();
                }
            }
        });
    }

    /// Substitutes variables with terms based on a unifier.
    pub fn subst_map(&mut self, map: &HashMap<usize, Term>) {
        self.apply_mut(&mut |v| {
            if let Self::Var(id) = v {
                if let Some(t) = map.get(id) {
                    *v = t.clone();
                }
            }
        });
    }

    /// Replaces a function with a variable.
    fn replace_func_to_var(&mut self, id: usize) {
        self.apply_mut(&mut |t| {
            if let Self::Func(f_id, _) = t {
                if *f_id == id {
                    *t = Self::Var(id);
                }
            }
        });
    }
}

impl Formula {
    /// Applies a function to the formula and its subformulas recursively.
    fn apply<F>(&self, f: &mut F)
    where
        F: FnMut(&Self),
    {
        f(self);
        use Formula::*;
        match self {
            Pred(..) => {}
            Not(p) => p.apply(f),
            And(l) | Or(l) => {
                for p in l {
                    p.apply(f);
                }
            }
            Implies(p, q) => {
                p.apply(f);
                q.apply(f);
            }
            All(_, p) | Exists(_, p) => {
                p.apply(f);
            }
        }
    }

    /// Applies a function to the formula and its subformulas recursively, allowing mutation of the formula.
    pub fn apply_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        f(self);
        use Formula::*;
        match self {
            Pred(..) => {}
            Not(p) => p.apply_mut(f),
            And(l) | Or(l) => {
                for p in l {
                    p.apply_mut(f);
                }
            }
            Implies(p, q) => {
                p.apply_mut(f);
                q.apply_mut(f);
            }
            All(_, p) | Exists(_, p) => {
                p.apply_mut(f);
            }
        }
    }

    /// Applies a function to the terms in the formula.
    fn apply_terms<F>(&self, f: &mut F)
    where
        F: FnMut(&Term),
    {
        self.apply(&mut |p| {
            if let Self::Pred(_, terms) = p {
                for term in terms {
                    f(term);
                }
            }
        });
    }

    /// Applies a function to the terms in the formula, allowing mutation of the terms.
    fn apply_terms_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Term),
    {
        self.apply_mut(&mut |p| {
            if let Self::Pred(_, terms) = p {
                for term in terms {
                    f(term);
                }
            }
        });
    }

    /// Collects function IDs in the formula.
    pub fn collect_func(&self) -> HashSet<usize> {
        let mut ids = hashset!();
        self.apply_terms(&mut |t| t.collect_func(&mut ids));
        ids
    }

    /// Collects predicate IDs in the formula.
    pub fn collect_pred(&self) -> HashSet<usize> {
        let mut ids = hashset!();
        self.apply(&mut |f| {
            if let Self::Pred(id, _) = f {
                ids.insert(*id);
            }
        });
        ids
    }

    /// Substitutes a variable with a new term.
    /// # Warning
    /// This method is implemented naively and may cause variable capture.
    pub fn subst(&mut self, var: usize, new_term: &Term) {
        self.apply_terms_mut(&mut |t| t.subst(var, new_term));
    }

    /// Substitutes variables with terms based on a unifier.
    /// # Warning
    /// This method is implemented naively and may cause variable capture.
    pub fn subst_map(&mut self, map: &HashMap<usize, Term>) {
        self.apply_terms_mut(&mut |t| t.subst_map(map));
    }

    // TODO: 2024/04/06 引数をskolem_idsにする
    pub fn replace_func_to_var(&mut self, id: usize) {
        use Formula::*;
        match self {
            Pred(_, terms) => {
                for term in terms {
                    term.replace_func_to_var(id);
                }
            }
            Not(p) => p.replace_func_to_var(id),
            And(l) | Or(l) => {
                for p in l {
                    p.replace_func_to_var(id);
                }
            }
            Implies(p, q) => {
                p.replace_func_to_var(id);
                q.replace_func_to_var(id);
            }
            All(_, p) | Exists(_, p) => {
                p.replace_func_to_var(id);
            }
        }
    }
}

#[cfg(test)]
mod tests {}
