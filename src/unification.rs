use crate::formula::Term;
use std::collections::HashMap;
use Term::*;

pub type Unifier = HashMap<usize, Term>;

#[derive(Debug, PartialEq)]
pub struct UnificationFailure;

impl Term {
    pub fn unify(&self, other: &Self, u: &mut Unifier) -> Result<(), UnificationFailure> {
        let t1 = &self.resolve(u).clone();
        let t2 = &other.resolve(u).clone();
        match (t1, t2) {
            (Var(v1), Var(v2)) if v1 == v2 => Ok(()),
            (Var(v), t) | (t, Var(v)) => {
                if t.has_fv(*v, u) {
                    return Err(UnificationFailure);
                }
                u.insert(*v, t.clone());
                Ok(())
            }
            (Func(id1, terms1), Func(id2, terms2)) => {
                if id1 != id2 || terms1.len() != terms2.len() {
                    return Err(UnificationFailure);
                }
                for (t1, t2) in terms1.iter().zip(terms2.iter()) {
                    t1.unify(t2, u)?;
                }
                Ok(())
            }
        }
    }

    fn resolve<'a>(&'a self, u: &'a Unifier) -> &'a Self {
        match self {
            Var(v) => u.get(v).map_or(self, |t| t.resolve(u)),
            _ => self,
        }
    }

    fn has_fv(&self, v: usize, u: &Unifier) -> bool {
        match self.resolve(u) {
            Var(j) => v == *j,
            Func(_, terms) => terms.iter().any(|t| t.has_fv(v, u)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{formula::Formula, parser::parse};
    use maplit::hashmap;
    use std::collections::HashMap;

    #[test]
    fn test_unify_suc1() {
        // x = f(y)
        let result = test_unify("x", "f(y)");
        // x ↦ f(y)
        let expected = hashmap!["x".into() => "f(y)".into()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_unify_suc2() {
        // f(x, g(y)) = f(g(z), w)
        let result = test_unify("f(x, g(y))", "f(g(z), w)");
        // x ↦ g(z), w ↦ g(y)
        let expected = hashmap!["x".into() => "g(z)".into(), "w".into() => "g(y)".into()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_unify_suc3() {
        // f(x, y) = f(y, x)
        let result = test_unify("f(x, y)", "f(y, x)");
        // x ↦ y
        let expected = hashmap!["x".into() => "y".into()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_unify_suc4() {
        // f(x, g(x)) = f(y, z)
        let result = test_unify("f(x, g(x))", "f(y, z)");
        // x ↦ y, z ↦ g(x)
        let expected = hashmap!["x".into() => "y".into(), "z".into() => "g(x)".into()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_unify_suc5() {
        // f(x, y, z, x) = f(y, z, g(u), g(v))
        let result = test_unify("f(x, y, z, x)", "f(y, z, g(u), g(v))");
        // x ↦ y, y ↦ z, z ↦ g(u), u ↦ v
        let expected = hashmap!["x".into() => "y".into(), "y".into() => "z".into(), "z".into() => "g(u)".into(), "u".into() => "v".into()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_unify_suc6() {
        // f(x, y, z, x) = f(y, z, u, v)
        let result = test_unify("f(x, y, z, x)", "f(y, z, u, v)");
        // x ↦ y, y ↦ z, z ↦ u, u ↦ v
        let expected = hashmap!["x".into() => "y".into(), "y".into() => "z".into(), "z".into() => "u".into(), "u".into() => "v".into()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_unify_fail1() {
        // f(x) = g(x)
        let result = test_unify("f(x)", "g(x)");
        // Fail
        assert_eq!(result, Err(UnificationFailure));
    }

    #[test]
    fn test_unify_fail2() {
        // x = f(y, g(z, x))
        let result = test_unify("x", "f(y, g(z, x))");
        // Fail
        assert_eq!(result, Err(UnificationFailure));
    }

    #[test]
    fn test_unify_fail3() {
        // f(y, y) = f(g(x), x)
        let result = test_unify("f(y, y)", "f(g(x), x)");
        // Fail
        assert_eq!(result, Err(UnificationFailure));
    }

    #[test]
    fn test_unify_fail4() {
        // f(x, y, z, x) = f(y, z, u, g(u))
        let result = test_unify("f(x, y, z, x)", "f(y, z, u, g(u))");
        // Fail
        assert_eq!(result, Err(UnificationFailure));
    }

    fn test_unify(s: &str, t: &str) -> Result<HashMap<String, String>, UnificationFailure> {
        let fml_str = format!("P({s}, {t})");
        let (fml, entities) = parse(&fml_str).unwrap();
        let fml = fml.universal_quantify();
        let Formula::All(vs, mut p) = fml else {
            unreachable!()
        };
        let mut new_id = entities.len();
        let mut free_var_info = hashmap!();
        for old_v in vs {
            p.subst(old_v, &Var(new_id));
            free_var_info.insert(new_id, old_v);
            new_id += 1;
        }
        let Formula::Predicate(_, terms) = *p else {
            unreachable!()
        };
        let t1 = terms[0].clone();
        let t2 = terms[1].clone();
        let mut u = hashmap!();
        t1.unify(&t2, &mut u)?;
        let mut result = hashmap!();
        for (new_v, t) in u.iter_mut() {
            for (new_v, old_v) in &free_var_info {
                t.subst(*new_v, &Var(*old_v));
            }
            let old_v = free_var_info[&new_v];
            result.insert(
                Var(old_v).display(&entities).to_string(),
                t.display(&entities).to_string(),
            );
        }
        Ok(result)
    }
}
