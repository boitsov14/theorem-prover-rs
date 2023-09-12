use enum_variant_type::EnumVariantType;
use maplit::hashset;
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

#[derive(Clone, Debug, EnumVariantType, Eq, Hash, PartialEq)]
pub enum Term {
    Var(usize),
    Function(usize, Vec<Term>),
}

#[derive(Clone, Debug, EnumVariantType, Eq, Hash, PartialEq)]
pub enum Formula {
    Predicate(usize, Vec<Term>),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    All(Vec<usize>, Box<Formula>),
    Exists(Vec<usize>, Box<Formula>),
}

pub static TRUE: Formula = Formula::And(vec![]);
pub static FALSE: Formula = Formula::Or(vec![]);

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NamingInfo {
    map: HashMap<String, usize>,
    id: usize,
}

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

    // TODO: 2023/08/25 pub or private
    /// Returns a string representation of the Term using the provided NamingInfo.
    pub fn to_str_inf(&self, inf: &NamingInfo) -> String {
        use Term::*;
        match self {
            Var(id) => inf.get_name(*id).into(),
            Function(id, terms) => {
                format!(
                    "{}({})",
                    inf.get_name(*id),
                    terms
                        .iter()
                        .map(|term| term.to_str_inf(inf))
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str_inf(&NamingInfo::new()))
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

impl Not {
    pub fn new(p: Formula) -> Self {
        Self(Box::new(p))
    }
}

impl Implies {
    pub fn new(p: Formula, q: Formula) -> Self {
        Self(Box::new(p), Box::new(q))
    }
}

impl Iff {
    pub fn new(p: Formula, q: Formula) -> Self {
        Self(Box::new(p), Box::new(q))
    }
}

impl All {
    pub fn new(vars: Vec<usize>, p: Formula) -> Self {
        Self(vars, Box::new(p))
    }
}

impl Exists {
    pub fn new(vars: Vec<usize>, p: Formula) -> Self {
        Self(vars, Box::new(p))
    }
}

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
            Implies(p, q) | Iff(p, q) => {
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

    /// Returns a string representation of the Formula using the provided NamingInfo.
    pub fn to_str_inf(&self, inf: &NamingInfo) -> String {
        let s = self.to_str_inf_rec(inf);
        s.strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or(&s)
            .into()
    }

    fn to_str_inf_rec(&self, inf: &NamingInfo) -> String {
        use Formula::*;
        match self {
            Predicate(id, terms) => {
                if terms.is_empty() {
                    inf.get_name(*id).into()
                } else {
                    format!(
                        "{}({})",
                        inf.get_name(*id),
                        terms
                            .iter()
                            .map(|term| term.to_str_inf(inf))
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                }
            }
            Not(p) => format!("¬{}", p.to_str_inf_rec(inf)),
            And(l) => {
                if l.is_empty() {
                    "true".into()
                } else {
                    format!(
                        "({})",
                        l.iter()
                            .map(|p| p.to_str_inf_rec(inf))
                            .collect::<Vec<_>>()
                            .join(" ∧ ")
                    )
                }
            }
            Or(l) => {
                if l.is_empty() {
                    "false".into()
                } else {
                    format!(
                        "({})",
                        l.iter()
                            .map(|p| p.to_str_inf_rec(inf))
                            .collect::<Vec<_>>()
                            .join(" ∨ ")
                    )
                }
            }
            Implies(p, q) => format!("({} → {})", p.to_str_inf_rec(inf), q.to_str_inf_rec(inf)),
            Iff(p, q) => format!("({} ↔ {})", p.to_str_inf_rec(inf), q.to_str_inf_rec(inf)),
            All(vars, p) => format!(
                "∀{}{}",
                vars.iter()
                    .map(|id| inf.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                p.to_str_inf_rec(inf)
            ),
            Exists(vars, p) => format!(
                "∃{}{}",
                vars.iter()
                    .map(|id| inf.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                p.to_str_inf_rec(inf)
            ),
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str_inf_rec(&NamingInfo::new()))
    }
}

impl Default for Formula {
    fn default() -> Self {
        TRUE.clone()
    }
}

impl NamingInfo {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_id(&mut self, s: String) -> usize {
        if let Some(&id) = self.map.get(&s) {
            id
        } else {
            self.id += 1;
            self.map.insert(s, self.id);
            self.id
        }
    }

    fn get_name(&self, id: usize) -> &str {
        self.map
            .iter()
            .find_map(
                |(key, val)| {
                    if *val == id {
                        Some(key.as_str())
                    } else {
                        None
                    }
                },
            )
            .expect("Value not found for id")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_id() {}

    #[test]
    fn test_get_name() {}

    #[test]
    fn test_write_str_var() {
        use Term::*;
        let mut inf = NamingInfo::new();
        let id = inf.get_id("x".into());
        let term = Var(id);
        assert_eq!(term.to_str_inf(&inf), "x");
    }

    // TODO: 2023/08/24 さすがに大変なのでパーサー使う
    #[test]
    fn test_write_str_function() {
        use Term::*;
        let mut inf = NamingInfo::new();
        let func_id = inf.get_id("f".into());
        let var_id_x = inf.get_id("x".into());
        let var_id_y = inf.get_id("y".into());
        let var_x = Var(var_id_x);
        let var_y = Var(var_id_y);
        let term = Function(func_id, vec![var_x, var_y]);
        assert_eq!(term.to_str_inf(&inf), "f(x,y)");
    }

    #[test]
    fn test_formula_write_str() {}
}
