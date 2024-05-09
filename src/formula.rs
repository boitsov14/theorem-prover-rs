use std::collections::HashMap;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Term {
    Var(usize),
    Func(usize, Vec<Term>),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Formula {
    Predicate(usize, Vec<Term>),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    All(Vec<usize>, Box<Formula>),
    Exists(Vec<usize>, Box<Formula>),
}

impl Term {
    pub fn subst(&mut self, var: usize, new_term: &Self) {
        use Term::*;
        match self {
            Var(id) => {
                if *id == var {
                    *self = new_term.clone();
                }
            }
            Func(_, terms) => {
                for term in terms {
                    term.subst(var, new_term);
                }
            }
        }
    }

    fn subst_unifier(&mut self, u: &HashMap<usize, Term>) {
        use Term::*;
        match self {
            Var(id) => {
                if let Some(t) = u.get(id) {
                    *self = t.clone();
                }
            }
            Func(_, terms) => {
                for term in terms {
                    term.subst_unifier(u);
                }
            }
        }
    }

    fn replace_func_to_var(&mut self, id: usize) {
        use Term::*;
        match self {
            Var(_) => {}
            Func(f_id, terms) => {
                if *f_id == id {
                    *self = Var(id);
                } else {
                    for term in terms {
                        term.replace_func_to_var(id);
                    }
                }
            }
        }
    }
}

impl Formula {
    pub fn subst(&mut self, var: usize, new_term: &Term) {
        use Formula::*;
        match self {
            Predicate(_, terms) => {
                for term in terms {
                    term.subst(var, new_term);
                }
            }
            Not(p) => p.subst(var, new_term),
            And(l) | Or(l) => {
                for p in l {
                    p.subst(var, new_term);
                }
            }
            Implies(p, q) => {
                p.subst(var, new_term);
                q.subst(var, new_term);
            }
            All(vs, p) | Exists(vs, p) => {
                if !vs.contains(&var) {
                    p.subst(var, new_term);
                }
            }
        }
    }

    pub fn subst_unifier(&mut self, u: &HashMap<usize, Term>) {
        use Formula::*;
        match self {
            Predicate(_, terms) => {
                for term in terms {
                    term.subst_unifier(u);
                }
            }
            Not(p) => p.subst_unifier(u),
            And(l) | Or(l) => {
                for p in l {
                    p.subst_unifier(u);
                }
            }
            Implies(p, q) => {
                p.subst_unifier(u);
                q.subst_unifier(u);
            }
            All(vs, p) | Exists(vs, p) => {
                // drop vs from u
                let mut u = u.clone();
                for v in vs {
                    u.remove(v);
                }
                p.subst_unifier(&u);
            }
        }
    }

    // TODO: 2024/04/06 引数をskolem_idsにする
    pub fn replace_func_to_var(&mut self, id: usize) {
        use Formula::*;
        match self {
            Predicate(_, terms) => {
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
