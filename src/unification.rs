use crate::formula::Term;
use Term::*;

type Unifier = Vec<Option<Term>>;

#[derive(Debug, PartialEq)]
struct UnificationFailure;

impl Term {
    fn unify(&self, other: &Self, u: &mut Unifier) -> Result<(), UnificationFailure> {
        let t1 = &self.resolve(u).clone();
        let t2 = &other.resolve(u).clone();
        match (t1, t2) {
            (Var(v1), Var(v2)) if v1 == v2 => Ok(()),
            (Var(v), t) | (t, Var(v)) => {
                if t.has_fv(*v, u) {
                    return Err(UnificationFailure);
                }
                u[*v] = Some(t.clone());
                Ok(())
            }
            (Func(id1, args1), Func(id2, args2)) => {
                if id1 != id2 || args1.len() != args2.len() {
                    return Err(UnificationFailure);
                }
                for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                    arg1.unify(arg2, u)?;
                }
                Ok(())
            }
        }
    }

    fn resolve<'a>(&'a self, u: &'a Unifier) -> &'a Self {
        match self {
            Var(v) => {
                if let Some(t) = &u[*v] {
                    t.resolve(u)
                } else {
                    self
                }
            }
            _ => self,
        }
    }

    fn has_fv(&self, v: usize, u: &Unifier) -> bool {
        match self.resolve(u) {
            Var(j) => v == *j,
            Func(_, args) => args.iter().any(|t| t.has_fv(v, u)),
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
    fn test_unify1() {
        // x = f(y)
        let result = test_unify("x", "f(y)");
        // x ↦ f(y)
        let expected = hashmap!["x".into() => Some("f(y)".into()), "y".into() => None];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_unify2() {
        // f(x, g(y)) = f(g(z), w)
        let result = test_unify("f(x, g(y))", "f(g(z), w)");
        // x ↦ g(z), w ↦ g(y)
        let expected = hashmap!["x".into() => Some("g(z)".into()), "w".into() => Some("g(y)".into()), "z".into() => None, "y".into() => None];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_unify3() {
        // f(x, y) = f(y, x)
        let result = test_unify("f(x, y)", "f(y, x)");
        // x ↦ y
        let expected = hashmap!["x".into() => Some("y".into()), "y".into() => None];
        assert_eq!(result, Ok(expected));
    }

    fn test_unify(s: &str, t: &str) -> Result<HashMap<String, Option<String>>, UnificationFailure> {
        let fml_str = format!("P({s}, {t})");
        let (fml, entities) = parse(&fml_str).unwrap();
        let fml = fml.universal_quantify();
        let Formula::All(vs, mut p) = fml else {
            unreachable!()
        };
        let mut free_var_idx = 0;
        let mut free_var_info = vec![];
        for v in vs {
            p.subst(v, &Var(free_var_idx));
            free_var_idx += 1;
            free_var_info.push(v);
        }
        let Formula::Predicate(_, args) = *p else {
            unreachable!()
        };
        let t1 = args[0].clone();
        let t2 = args[1].clone();
        let mut u = vec![None; free_var_idx];
        t1.unify(&t2, &mut u)?;
        let mut result = hashmap!();
        for (new_v, t) in u.iter().enumerate() {
            let old_v = free_var_info[new_v];
            let old_v_str = Var(old_v).display(&entities).to_string();
            if let Some(t) = t {
                let mut t = t.clone();
                for (new_v, old_v) in free_var_info.iter().enumerate() {
                    t.subst(new_v, &Var(*old_v));
                }
                result.insert(old_v_str, Some(t.display(&entities).to_string()));
            } else {
                result.insert(old_v_str, None);
            }
        }
        Ok(result)
    }
}
