use enum_variant_type::EnumVariantType;
use maplit::hashset;
use std::collections::{HashMap, HashSet};

// TODO: 2023/07/06 Dummyどうしの比較は常にNot Eqになってほしい
#[derive(Clone, Debug, EnumVariantType, Eq, Hash, PartialEq)]
pub enum Term {
    Var(VarID),
    UnificationTerm(UnificationTermID),
    Function(String, Vec<Term>),
    Dummy,
}

type VarID = String;
type UnificationTermID = (usize, usize);

impl Term {
    pub fn get_free_vars(&self) -> HashSet<&VarID> {
        let mut free_vars = HashSet::new();
        use Term::*;
        match self {
            Var(id) => {
                free_vars.insert(id);
            }
            UnificationTerm(_) | Dummy => {}
            Function(_, terms) => {
                for term in terms {
                    free_vars.extend(term.get_free_vars())
                }
            }
        }
        free_vars
    }

    pub fn get_free_vars2(&self) -> HashSet<&VarID> {
        use Term::*;
        match self {
            Var(id) => hashset!(id),
            UnificationTerm(_) | Dummy => hashset!(),
            Function(_, terms) => terms
                .iter()
                .flat_map(|term| term.get_free_vars2())
                .collect(),
        }
    }

    fn get_unification_terms(&self) -> HashSet<&UnificationTermID> {
        let mut unification_terms = HashSet::new();
        use Term::*;
        match self {
            Var(_) | Dummy => {}
            UnificationTerm(id) => {
                unification_terms.insert(id);
            }
            Function(_, terms) => {
                for term in terms {
                    unification_terms.extend(term.get_unification_terms())
                }
            }
        }
        unification_terms
    }

    // TODO: 2023/07/06 所有権をどうするか
    // TODO: 2023/07/06 VarIDかVarか
    pub fn replace_var(self, var_id: &VarID, new_term: &Self) -> Self {
        use Term::*;
        match self {
            Var(id) => {
                if &id == var_id {
                    new_term.clone()
                } else {
                    Var(id)
                }
            }
            UnificationTerm(_) | Dummy => self,
            Function(id, terms) => {
                let terms = terms
                    .into_iter()
                    .map(|term| term.replace_var(var_id, new_term))
                    .collect();
                Function(id, terms)
            }
        }
    }

    pub fn replace_unification_term(
        self,
        unification_term_id: &UnificationTermID,
        new_term: &Self,
    ) -> Self {
        use Term::*;
        match self {
            Var(_) | Dummy => self,
            UnificationTerm(id) => {
                if &id == unification_term_id {
                    new_term.clone()
                } else {
                    UnificationTerm(id)
                }
            }
            Function(id, terms) => {
                let terms = terms
                    .into_iter()
                    .map(|term| term.replace_unification_term(unification_term_id, new_term))
                    .collect();
                Function(id, terms)
            }
        }
    }

    pub fn replace_unification_terms(self, map: &HashMap<UnificationTermID, Self>) -> Self {
        use Term::*;
        match self {
            Var(_) | Dummy => self,
            UnificationTerm(id) => {
                if let Some(new_term) = map.get(&id) {
                    new_term.clone()
                } else {
                    UnificationTerm(id)
                }
            }
            Function(id, terms) => {
                let terms = terms
                    .into_iter()
                    .map(|term| term.replace_unification_terms(map))
                    .collect();
                Function(id, terms)
            }
        }
    }

    // TODO: 2023/07/06 to_str的なのを書く
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Term::*;
        match self {
            Var(id) => write!(f, "{id}"),
            UnificationTerm((id1, id2)) => write!(f, "t({id1}, {id2})"),
            Function(name, terms) => {
                write!(
                    f,
                    "{name}({})",
                    terms
                        .iter()
                        .map(|term| format!("{}", term))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
                // write!(f, "{name}(")?;
                // for (i, term) in terms.iter().enumerate() {
                //     if i > 0 {
                //         write!(f, ", ")?;
                //     }
                //     write!(f, "{}", term)?;
                // }
                // write!(f, ")")
            }
            Dummy => write!(f, "_"),
        }
    }
}

impl Var {
    fn get_fresh_var(self, old_vars: HashSet<&VarID>) -> Var {
        let Var(id) = self;
        if old_vars.contains(&id) {
            Var(id + "'").get_fresh_var(old_vars)
        } else {
            Var(id)
        }
    }
}
