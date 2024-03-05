use crate::formula::Term;
use Term::*;

type Unifier = Vec<Option<Term>>;

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
