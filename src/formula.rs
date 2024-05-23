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
    To(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    All(Vec<usize>, Box<Formula>),
    Ex(Vec<usize>, Box<Formula>),
}

#[derive(Clone, Debug)]
pub(super) struct Sequent {
    pub(super) ant: Vec<Formula>,
    pub(super) suc: Vec<Formula>,
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
        if let Self::Func(_, ts) = self {
            for t in ts {
                t.visit_mut(f);
            }
        }
        f(self);
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
    /// Replaces a function with a variable of the same ID.
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
    fn visit_children<F>(&self, mut f: F)
    where
        F: FnMut(&Self),
    {
        use Formula::*;
        match self {
            Pred(..) => {}
            Not(p) => f(p),
            And(l) | Or(l) => {
                l.iter().for_each(&mut f);
            }
            To(p, q) | Iff(p, q) => {
                f(p);
                f(q);
            }
            All(_, p) | Ex(_, p) => {
                f(p);
            }
        }
    }

    /// Visits and applies a function to the children of the formula, allowing mutation of the formula.
    pub(super) fn visit_children_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Self),
    {
        use Formula::*;
        match self {
            Pred(..) => {}
            Not(p) => f(p),
            And(l) | Or(l) => {
                l.iter_mut().for_each(&mut f);
            }
            To(p, q) | Iff(p, q) => {
                f(p);
                f(q);
            }
            All(_, p) | Ex(_, p) => {
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
        self.visit_children(|p| p.visit(f));
    }

    /// Visits and applies a function to the formula and its subformulas recursively, allowing mutation of the formula.
    pub(super) fn visit_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        self.visit_children_mut(|p| p.visit_mut(f));
        f(self);
    }

    /// Visits and applies a function to all terms in the formula.
    pub(super) fn visit_terms<F>(&self, mut f: F)
    where
        F: FnMut(&Term),
    {
        self.visit(&mut |p| {
            let Self::Pred(_, ts) = p else { return };
            ts.iter().for_each(&mut f);
        });
    }

    /// Visits and applies a function to all terms in the formula, allowing mutation of the terms.
    fn visit_terms_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Term),
    {
        self.visit_mut(&mut |p| {
            let Self::Pred(_, ts) = p else { return };
            ts.iter_mut().for_each(&mut f);
        });
    }

    /// Substitutes a variable with a new term.
    /// # Warning
    /// This method is implemented naively and may cause variable capture.
    pub(super) fn subst(&mut self, var: usize, new_term: &Term) {
        self.visit_terms_mut(|t| t.subst(var, new_term));
    }

    /// Substitutes variables with terms.
    /// # Warning
    /// This method is implemented naively and may cause variable capture.
    pub(super) fn subst_map(&mut self, map: &HashMap<usize, Term>) {
        self.visit_terms_mut(|t| t.subst_map(map));
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
            To(p, q) | Iff(p, q) => {
                p.replace_func_with_var(id);
                q.replace_func_with_var(id);
            }
            All(_, p) | Ex(_, p) => {
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

impl Sequent {
    /// Visits and applies a function to all formulas in the sequent.
    pub(super) fn visit_formulas<F>(&self, mut f: F)
    where
        F: FnMut(&Formula),
    {
        self.ant.iter().for_each(&mut f);
        self.suc.iter().for_each(&mut f);
    }

    /// Visits and applies a function to all formulas in the sequent, allowing mutation of the formulas.
    pub(super) fn visit_formulas_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Formula),
    {
        self.ant.iter_mut().for_each(&mut f);
        self.suc.iter_mut().for_each(&mut f);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        naming::Names,
        parser::{parse_formula, parse_term},
        paste, test,
    };

    /// Tests for `Term::subst`
    fn term_subst(term: &str, var: &str, subterm: &str, expected: &str) {
        let mut names = Names::default();
        let mut term = parse_term(term, &mut names).unwrap();
        let var = names.get_id(var.into());
        let subterm = parse_term(subterm, &mut names).unwrap();
        term.subst(var, &subterm);
        let expected = parse_term(expected, &mut names).unwrap();
        assert_eq!(term, expected);
    }
    /// Tests for `Term::subst_map`
    fn term_subst_map(term: &str, map: &[(&str, &str)], expected: &str) {
        let mut names = Names::default();
        let mut term = parse_term(term, &mut names).unwrap();
        let map = map
            .iter()
            .map(|(k, v)| {
                (
                    names.get_id(k.to_string()),
                    parse_term(v, &mut names).unwrap(),
                )
            })
            .collect();
        term.subst_map(&map);
        let expected = parse_term(expected, &mut names).unwrap();
        assert_eq!(term, expected);
    }
    /// Tests for `Formula::subst`
    fn fml_subst(fml: &str, var: &str, term: &str, expected: &str) {
        let mut names = Names::default();
        let mut fml = parse_formula(fml, &mut names, false).unwrap();
        let term = parse_term(term, &mut names).unwrap();
        let var = names.get_id(var.into());
        fml.subst(var, &term);
        let expected = parse_formula(expected, &mut names, false).unwrap();
        assert_eq!(fml, expected);
    }
    /// Tests for `Formula::subst_map`
    fn fml_subst_map(fml: &str, map: &[(&str, &str)], expected: &str) {
        let mut names = Names::default();
        let mut fml = parse_formula(fml, &mut names, false).unwrap();
        let map = map
            .iter()
            .map(|(k, v)| {
                (
                    names.get_id(k.to_string()),
                    parse_term(v, &mut names).unwrap(),
                )
            })
            .collect();
        fml.subst_map(&map);
        let expected = parse_formula(expected, &mut names, false).unwrap();
        assert_eq!(fml, expected);
    }

    // Tests for `Term::subst`
    test!(term_subst, 1, "x", "x", "f(y)", "f(y)");
    test!(term_subst, 2, "x", "x", "f(x)", "f(x)");
    test!(term_subst, 3, "f(x,g(y))", "y", "h(x,y)", "f(x,g(h(x,y)))");
    // Tests for `Term::subst_map`
    test!(term_subst_map, 1, "x", &[("x", "f(y)")], "f(y)");
    test!(term_subst_map, 2, "x", &[("x", "f(x)")], "f(x)");
    test!(
        term_subst_map,
        3,
        "h(z,f(x,g(y)))",
        &[("y", "h(x,y)"), ("z", "i(a,b)")],
        "h(i(a,b),f(x,g(h(x,y))))"
    );
    // Tests for `Formula::subst`
    test!(fml_subst, 1, "P(x)", "x", "f(y)", "P(f(y))");
    test!(fml_subst, 2, "P(x)", "x", "f(x)", "P(f(x))");
    test!(fml_subst, 3, "P(x,g(y))", "y", "h(x,y)", "P(x,g(h(x,y)))");
    test!(fml_subst, 4, "∀xP(x)", "x", "f(y)", "∀xP(f(y))");
    test!(fml_subst, 5, "∀xP(x)", "x", "f(x)", "∀xP(f(x))");
    test!(
        fml_subst,
        6,
        "(((¬P(x) ∧ Q(x)) ∨ R(x)) → S(x)) → T(x)",
        "x",
        "f(y)",
        "(((¬P(f(y)) ∧ Q(f(y))) ∨ R(f(y))) → S(f(y))) → T(f(y))"
    );
    // Tests for `Formula::subst_map`
}
