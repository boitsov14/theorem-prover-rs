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

impl Term {
    fn free_vars(&self) -> HashSet<usize> {
        let mut vars = hashset!();
        self.free_vars_rec(&mut vars);
        vars
    }

    fn free_vars_rec(&self, vars: &mut HashSet<usize>) {
        use Term::*;
        match self {
            Var(id) => {
                vars.insert(*id);
            }
            Function(_, terms) => {
                for term in terms {
                    term.free_vars_rec(vars);
                }
            }
        }
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

    // TODO: 2023/08/25 pub or private
    // TODO: 2023/08/28 to_stringにするか
    /// Returns a string representation of the Term using the provided NamingInfo.
    pub fn write_str(&self, inf: &NamingInfo) -> String {
        use Term::*;
        match self {
            Var(id) => inf.get_name(*id).to_string(),
            Function(id, terms) => {
                format!(
                    "{}({})",
                    inf.get_name(*id),
                    terms
                        .iter()
                        .map(|term| term.write_str(inf))
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
        }
    }
}

// TODO: 2023/08/21 そもそもこれは必要なのか
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Term::*;
        match self {
            Var(id) => write!(f, "{id}"),
            Function(id, terms) => {
                write!(
                    f,
                    "{id}({})",
                    terms
                        .iter()
                        .map(|term| format!("{term}"))
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
        }
    }
}

// TODO: 2023/08/21 型や所有権は要検討
fn get_new_sig(sig: String, set: &HashSet<String>) -> String {
    if set.contains(&sig) {
        get_new_sig(sig + "'", set)
    } else {
        sig
    }
}

impl Formula {
    // TODO: 2023/08/28 TrueとFalseの場合
    pub fn write_str(&self, inf: &NamingInfo) -> String {
        use Formula::*;
        match self {
            Predicate(id, terms) => {
                if terms.is_empty() {
                    inf.get_name(*id).to_string()
                } else {
                    format!(
                        "{}({})",
                        inf.get_name(*id),
                        terms
                            .iter()
                            .map(|term| term.write_str(inf))
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                }
            }
            Not(fml) => format!("¬{}", fml.write_str(inf)),
            And(fmls) => format!(
                "({})",
                fmls.iter()
                    .map(|fml| fml.write_str(inf))
                    .collect::<Vec<_>>()
                    .join(" ∧ ")
            ),
            Or(fmls) => format!(
                "({})",
                fmls.iter()
                    .map(|fml| fml.write_str(inf))
                    .collect::<Vec<_>>()
                    .join(" ∨ ")
            ),
            Implies(lhs, rhs) => format!("({} → {})", lhs.write_str(inf), rhs.write_str(inf)),
            Iff(lhs, rhs) => format!("({} ↔ {})", lhs.write_str(inf), rhs.write_str(inf)),
            All(vars, fml) => format!(
                "∀{}{}",
                vars.iter()
                    .map(|id| inf.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                fml.write_str(inf)
            ),
            Exists(vars, fml) => format!(
                "∃{}{}",
                vars.iter()
                    .map(|id| inf.get_name(*id))
                    .collect::<Vec<_>>()
                    .join(","),
                fml.write_str(inf)
            ),
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Formula::*;
        match self {
            Predicate(id, terms) => {
                if terms.is_empty() {
                    write!(f, "{id}")
                } else {
                    write!(
                        f,
                        "{id}({})",
                        terms
                            .iter()
                            .map(|term| format!("{term}"))
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                }
            }
            Not(fml) => write!(f, "¬{fml}"),
            And(fmls) => write!(
                f,
                "({})",
                fmls.iter()
                    .map(|fml| format!("{fml}"))
                    .collect::<Vec<_>>()
                    .join(" ∧ ")
            ),
            Or(fmls) => write!(
                f,
                "({})",
                fmls.iter()
                    .map(|fml| format!("{fml}"))
                    .collect::<Vec<_>>()
                    .join(" ∨ ")
            ),
            Implies(lhs, rhs) => write!(f, "({lhs} → {rhs})"),
            Iff(lhs, rhs) => write!(f, "({lhs} ↔ {rhs})"),
            All(vars, fml) => write!(
                f,
                "∀{}{fml}",
                vars.iter()
                    .map(|term| format!("{term}"))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Exists(vars, fml) => write!(
                f,
                "∃{}{fml}",
                vars.iter()
                    .map(|term| format!("{term}"))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        }
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
        let id = inf.get_id("x".to_string());
        let term = Var(id);
        assert_eq!(term.write_str(&inf), "x");
    }

    // TODO: 2023/08/24 さすがに大変なのでパーサー使う
    #[test]
    fn test_write_str_function() {
        use Term::*;
        let mut inf = NamingInfo::new();
        let func_id = inf.get_id("f".to_string());
        let var_id_x = inf.get_id("x".to_string());
        let var_id_y = inf.get_id("y".to_string());
        let var_x = Var(var_id_x);
        let var_y = Var(var_id_y);
        let term = Function(func_id, vec![var_x, var_y]);
        assert_eq!(term.write_str(&inf), "f(x, y)");
    }

    #[test]
    fn test_formula_write_str() {}
}
