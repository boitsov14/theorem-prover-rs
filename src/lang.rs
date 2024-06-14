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
pub struct Sequent {
    pub ant: Vec<Formula>,
    pub suc: Vec<Formula>,
}

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
}

impl Default for Formula {
    /// Returns `True`.
    fn default() -> Self {
        Formula::And(vec![])
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
    };
    use test_case::case;

    #[case("x", "x", "f(y)" => "f(y)")]
    #[case("x", "x", "f(x)" => "f(x)")]
    #[case("f(x,x,x)", "x", "g(y)" => "f(g(y),g(y),g(y))")]
    #[case("f(x,g(y))", "y", "h(x,y)" => "f(x,g(h(x,y)))")]
    fn term_subst(term: &str, var: &str, subterm: &str) -> String {
        let mut names = Names::default();
        let mut term = parse_term(term, &mut names).unwrap();
        let var = names.get_id(var.into());
        let subterm = parse_term(subterm, &mut names).unwrap();
        term.subst(var, &subterm);
        term.display(&names).to_string()
    }

    #[case("x", &[("x", "f(y)")] => "f(y)")]
    #[case("x", &[("x", "f(x)")] => "f(x)")]
    #[case("f(x,y,z)", &[("x", "g(u)"), ("y", "h(v)"), ("z", "i(w)")] => "f(g(u),h(v),i(w))")]
    #[case("x", &[("x", "y"), ("y", "z")] => "y")]
    #[case("h(z,f(x,g(y)))", &[("y", "h(x,y)"), ("z", "i(u,v)")] => "h(i(u,v),f(x,g(h(x,y))))")]
    fn term_subst_map(term: &str, map: &[(&str, &str)]) -> String {
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
        term.display(&names).to_string()
    }

    #[case("P(x)", "x", "f(y)" => "P(f(y))")]
    #[case("P(x)", "x", "f(x)" => "P(f(x))")]
    #[case("P(x,x,x)", "x", "g(y)" => "P(g(y),g(y),g(y))")]
    #[case("P(x,g(y))", "y", "h(x,y)" => "P(x,g(h(x,y)))")]
    #[case("∀xP(x)", "x", "y" => "∀xP(y)")]
    #[case("∀xP(x)", "x", "f(x)" => "∀xP(f(x))")]
    #[case("∀xP(y)", "y", "x" => "∀xP(x)")]
    #[case("(((¬P(x) ∧ Q(x)) ∨ R(x)) → S(x)) → T(x)", "x", "f(y)" => "(((¬P(f(y)) ∧ Q(f(y))) ∨ R(f(y))) → S(f(y))) → T(f(y))")]
    fn fml_subst(fml: &str, var: &str, term: &str) -> String {
        let mut names = Names::default();
        let mut fml = parse_formula(fml, &mut names, false).unwrap();
        let var = names.get_id(var.into());
        let term = parse_term(term, &mut names).unwrap();
        fml.subst(var, &term);
        fml.display(&names).to_string()
    }

    #[case("P(x)", &[("x", "f(y)")] => "P(f(y))")]
    #[case("P(x)", &[("x", "f(x)")] => "P(f(x))")]
    #[case("P(x,y,z)", &[("x", "g(u)"), ("y", "h(v)"), ("z", "i(w)")] => "P(g(u),h(v),i(w))")]
    #[case("P(x)", &[("x", "y"), ("y", "z")] => "P(y)")]
    #[case("P(x,g(y))", &[("y", "h(x,y)")] => "P(x,g(h(x,y)))")]
    #[case("∀xP(x)", &[("x", "y")] => "∀xP(y)")]
    #[case("∀xP(x)", &[("x", "f(x)")] => "∀xP(f(x))")]
    #[case("∀xP(y)", &[("y", "x")] => "∀xP(x)")]
    #[case("(((¬P(x) ∧ Q(z)) ∨ R(x)) → S(x)) → T(x)", &[("x", "f(y)"), ("z", "i(u,v)")] => "(((¬P(f(y)) ∧ Q(i(u,v))) ∨ R(f(y))) → S(f(y))) → T(f(y))")]
    fn fml_subst_map(fml: &str, map: &[(&str, &str)]) -> String {
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
        fml.display(&names).to_string()
    }
}
