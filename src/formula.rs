use maplit::hashset;
use std::collections::HashSet;

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
    fn fv(&self, vars: &mut HashSet<usize>) {
        use Term::*;
        match self {
            Var(id) => {
                vars.insert(*id);
            }
            Func(_, terms) => {
                for term in terms {
                    term.fv(vars);
                }
            }
        }
    }

    fn subst(&mut self, var: usize, new_term: &Term) {
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
}

/*
// TODO: 2023/08/21 型や所有権は要検討
fn get_new_sig(sig: String, set: &HashSet<String>) -> String {
    if set.contains(&sig) {
        get_new_sig(sig + "'", set)
    } else {
        sig
    }
}
*/

impl Formula {
    // TODO: 2023/09/06 parserでしか使用しないなら移動
    /// Returns all the free variables of the formula.
    pub fn free_vars(&self) -> HashSet<usize> {
        let mut vars = hashset!();
        self.fv(&mut vars);
        vars
    }

    fn fv(&self, vars: &mut HashSet<usize>) {
        use Formula::*;
        match self {
            Predicate(_, terms) => {
                for term in terms {
                    term.fv(vars);
                }
            }
            Not(p) => p.fv(vars),
            And(l) | Or(l) => {
                for p in l {
                    p.fv(vars);
                }
            }
            Implies(p, q) => {
                p.fv(vars);
                q.fv(vars);
            }
            All(vs, p) | Exists(vs, p) => {
                p.fv(vars);
                for v in vs {
                    vars.remove(v);
                }
            }
        }
    }

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
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    #[test]
    fn test_fv() {
        let (fml, mut entities) = parse("P(x)").unwrap();
        assert_eq!(
            fml.free_vars(),
            ["x"]
                .map(|s| entities.get_id(s.into()))
                .into_iter()
                .collect()
        );

        let (fml, mut entities) = parse("P(x, f(y,z))").unwrap();
        assert_eq!(
            fml.free_vars(),
            ["x", "y", "z"]
                .map(|s| entities.get_id(s.into()))
                .into_iter()
                .collect()
        );

        let (fml, mut entities) = parse("all x,y P(x, f(y,z))").unwrap();
        assert_eq!(
            fml.free_vars(),
            ["z"]
                .map(|s| entities.get_id(s.into()))
                .into_iter()
                .collect()
        );

        let (fml, mut entities) = parse("P(x) and Q(y) iff not R(z)").unwrap();
        assert_eq!(
            fml.free_vars(),
            ["x", "y", "z"]
                .map(|s| entities.get_id(s.into()))
                .into_iter()
                .collect()
        );
    }
}
