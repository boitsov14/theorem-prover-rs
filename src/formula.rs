use std::collections::HashMap;

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

static TRUE: Formula = Formula::And(vec![]);

impl Term {
    /// Visits and applies a function to the term and its subterms recursively.
    pub(super) fn visit<F>(&self, f: &mut F)
    where
        F: FnMut(&Self),
    {
        f(self);
        let Self::Func(_, ts) = self else { return };
        for t in ts {
            t.visit(f);
        }
    }

    /// Visits and applies a function to the term and its subterms recursively, allowing mutation of the term.
    pub(super) fn visit_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        f(self);
        let Self::Func(_, ts) = self else { return };
        for t in ts {
            t.visit_mut(f);
        }
    }

    /// Substitutes a variable with a term.
    fn subst(&mut self, var: usize, term: &Self) {
        self.visit_mut(&mut |v| {
            let Self::Var(id) = v else { return };
            if *id == var {
                *v = term.clone();
            }
        });
    }

    /// Substitutes variables with terms.
    pub(super) fn subst_map(&mut self, map: &HashMap<usize, Term>) {
        self.visit_mut(&mut |v| {
            let Self::Var(id) = v else { return };
            let Some(t) = map.get(id) else { return };
            *v = t.clone();
        });
    }

    // TODO: 2024/05/12 移動
    /// Replaces a function with a variable with the same ID.
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
    /// Visits and applies a function to the children of the formula.
    fn visit_children<F>(&self, f: &mut F)
    where
        F: FnMut(&Self),
    {
        use Formula::*;
        match self {
            Pred(..) => {}
            Not(p) => f(p),
            And(l) | Or(l) => {
                for p in l {
                    f(p);
                }
            }
            Implies(p, q) => {
                f(p);
                f(q);
            }
            All(_, p) | Exists(_, p) => {
                f(p);
            }
        }
    }

    /// Visits and applies a function to the children of the formula, allowing mutation of the formula.
    fn visit_children_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        use Formula::*;
        match self {
            Pred(..) => {}
            Not(p) => f(p),
            And(l) | Or(l) => {
                for p in l {
                    f(p);
                }
            }
            Implies(p, q) => {
                f(p);
                f(q);
            }
            All(_, p) | Exists(_, p) => {
                f(p);
            }
        }
    }

    /// Visits and applies a function to the formula and its subformulas recursively.
    pub(super) fn visit<F>(&self, f: &mut F)
    where
        F: FnMut(&Self),
    {
        f(self);
        self.visit_children(&mut |p| p.visit(f));
    }

    /// Visits and applies a function to the formula and its subformulas recursively, allowing mutation of the formula.
    pub(super) fn visit_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        f(self);
        self.visit_children_mut(&mut |p| p.visit_mut(f));
    }

    /// Visits and applies a function to all terms in the formula.
    pub(super) fn visit_terms<F>(&self, f: &mut F)
    where
        F: FnMut(&Term),
    {
        self.visit(&mut |p| {
            let Self::Pred(_, ts) = p else { return };
            for t in ts {
                f(t);
            }
        });
    }

    /// Visits and applies a function to all terms in the formula, allowing mutation of the terms.
    fn visit_terms_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Term),
    {
        self.visit_mut(&mut |p| {
            let Self::Pred(_, ts) = p else { return };
            for t in ts {
                f(t);
            }
        });
    }

    /// Substitutes a variable with a new term.
    /// # Warning
    /// This method is implemented naively and may cause variable capture.
    pub(super) fn subst(&mut self, var: usize, new_term: &Term) {
        self.visit_terms_mut(&mut |t| t.subst(var, new_term));
    }

    /// Substitutes variables with terms based on a unifier.
    /// # Warning
    /// This method is implemented naively and may cause variable capture.
    pub(super) fn subst_map(&mut self, map: &HashMap<usize, Term>) {
        self.visit_terms_mut(&mut |t| t.subst_map(map));
    }

    // TODO: 2024/05/13 移動
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
            Implies(p, q) => {
                p.replace_func_with_var(id);
                q.replace_func_with_var(id);
            }
            All(_, p) | Exists(_, p) => {
                p.replace_func_with_var(id);
            }
        }
    }
}

impl Default for Formula {
    fn default() -> Self {
        TRUE.clone()
    }
}

#[cfg(test)]
mod tests {
    // TODO: 2024/05/10 subst, subst_mapのテストを書く
}
