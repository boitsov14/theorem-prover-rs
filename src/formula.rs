use maplit::hashset;
use std::collections::HashSet;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Term {
    Var(usize),
    Function(usize, Vec<Term>),
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

pub static TRUE: Formula = Formula::And(vec![]);
pub static FALSE: Formula = Formula::Or(vec![]);

impl Term {
    fn fv(&self, vars: &mut HashSet<usize>) {
        use Term::*;
        match self {
            Var(id) => {
                vars.insert(*id);
            }
            Function(_, terms) => {
                for term in terms {
                    term.fv(vars);
                }
            }
        }
    }

    /*
    // TODO: 2023/09/06 いらないかも
    fn free_vars(&self) -> HashSet<usize> {
        let mut vars = hashset!();
        self.fv(&mut vars);
        vars
    }
    // TODO: 2023/07/06 所有権をどうするか
    // TODO: 2023/08/22 &mut selfとの比較
    // TODO: 2023/08/22 そもそも必要か：substitutionだけでよいのでは
    // TODO: 2023/08/22 subst_varの方がいい？
    fn replace_var(self, var: usize, new_term: &Self) -> Self {
        use Term::*;
        match self {
            Var(id) => {
                if id == var {
                    new_term.clone()
                } else {
                    Var(id)
                }
            }
            Function(id, terms) => {
                let terms = terms
                    .into_iter()
                    .map(|term| term.replace_var(var, new_term))
                    .collect();
                Function(id, terms)
            }
        }
    }

    fn replace_var2(&mut self, var: usize, new_term: &Self) {
        use Term::*;
        match self {
            Var(id) => {
                if *id == var {
                    *self = new_term.clone();
                }
            }
            Function(_, terms) => {
                for term in terms {
                    term.replace_var2(var, new_term);
                }
            }
        }
    }

    fn replace_vars(self, map: &HashMap<usize, Self>) -> Self {
        use Term::*;
        match self {
            Var(id) => {
                if let Some(new_term) = map.get(&id) {
                    new_term.clone()
                } else {
                    Var(id)
                }
            }
            Function(id, terms) => {
                let terms = terms
                    .into_iter()
                    .map(|term| term.replace_vars(map))
                    .collect();
                Function(id, terms)
            }
        }
    }
    */
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
}

impl Default for Formula {
    fn default() -> Self {
        TRUE.clone()
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    #[test]
    fn test_fv() {
        let (fml, mut inf) = parse("P(x)").unwrap();
        assert_eq!(
            fml.free_vars(),
            ["x"].map(|s| inf.get_id(s.into())).into_iter().collect()
        );

        let (fml, mut inf) = parse("P(x, f(y,z))").unwrap();
        assert_eq!(
            fml.free_vars(),
            ["x", "y", "z"]
                .map(|s| inf.get_id(s.into()))
                .into_iter()
                .collect()
        );

        let (fml, mut inf) = parse("all x,y P(x, f(y,z))").unwrap();
        assert_eq!(
            fml.free_vars(),
            ["z"].map(|s| inf.get_id(s.into())).into_iter().collect()
        );

        let (fml, mut inf) = parse("P(x) and Q(y) iff not R(z)").unwrap();
        assert_eq!(
            fml.free_vars(),
            ["x", "y", "z"]
                .map(|s| inf.get_id(s.into()))
                .into_iter()
                .collect()
        );
    }
}
