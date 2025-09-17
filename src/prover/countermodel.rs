use crate::{
    core::syntax::Formula,
    prover::sequent::{Sequent, Side::*, SidedFormula},
};
use ThreeValue::*;
use rustc_hash::FxHashSet;
use std::fmt;

/// Three-valued logic
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThreeValue {
    True,
    False,
    Undefined,
}

impl ThreeValue {
    const fn and(self, other: Self) -> Self {
        match (self, other) {
            (True, True) => True,
            (False, _) | (_, False) => False,
            _ => Undefined,
        }
    }

    const fn or(self, other: Self) -> Self {
        match (self, other) {
            (True, _) | (_, True) => True,
            (False, False) => False,
            _ => Undefined,
        }
    }

    const fn not(self) -> Self {
        match self {
            True => False,
            False => True,
            Undefined => Undefined,
        }
    }

    const fn implies(self, other: Self) -> Self {
        // p → q is equivalent to ¬p ∨ q
        self.not().or(other)
    }

    pub const fn iff(self, other: Self) -> Self {
        // p ↔ q is equivalent to (p → q) ∧ (q → p)
        self.implies(other).and(other.implies(self))
    }
}

impl fmt::Display for ThreeValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            True => write!(f, "True"),
            False => write!(f, "False"),
            Undefined => write!(f, "Undefined"),
        }
    }
}

/// A pair of formula and its evaluation result
#[derive(Clone, Debug)]
pub struct FormulaEvaluation<'a> {
    /// Formula being evaluated
    pub fml: &'a Formula,
    /// Evaluation result
    pub val: ThreeValue,
}

/// Countermodel representing truth assignments for atoms
#[derive(Clone, Debug)]
pub struct CounterModel {
    /// Left side atoms
    pub true_atoms: FxHashSet<usize>,
    /// Right side atoms
    pub false_atoms: FxHashSet<usize>,
}

impl CounterModel {
    pub fn new() -> Self {
        Self {
            true_atoms: FxHashSet::default(),
            false_atoms: FxHashSet::default(),
        }
    }

    /// Gets the three-valued logic value for an atom
    pub fn get_value(&self, atom: usize) -> ThreeValue {
        if self.true_atoms.contains(&atom) {
            ThreeValue::True
        } else if self.false_atoms.contains(&atom) {
            ThreeValue::False
        } else {
            ThreeValue::Undefined
        }
    }

    /// Evaluates a formula and creates a truth table, showing all subformula evaluations
    pub fn evaluate<'a>(&self, formula: &'a Formula) -> Vec<FormulaEvaluation<'a>> {
        let mut table = vec![];
        self.evaluate_recursive(formula, &mut table);
        table
    }

    /// Recursively evaluates a formula and fills the truth table
    fn evaluate_recursive<'a>(
        &self,
        fml: &'a Formula,
        table: &mut Vec<FormulaEvaluation<'a>>,
    ) -> ThreeValue {
        use Formula::*;

        let val = match fml {
            // get its value from the countermodel
            Pred(id, _) => self.get_value(*id),

            // evaluate subformula and negate
            Not(p) => {
                let val = self.evaluate_recursive(p, table);
                val.not()
            }

            // evaluate all subformulas and apply `and`
            And(l) => {
                let mut val = ThreeValue::True;
                for p in l {
                    let val_p = self.evaluate_recursive(p, table);
                    val = val.and(val_p);
                }
                val
            }

            // evaluate all subformulas and apply `or`
            Or(l) => {
                let mut val = ThreeValue::False;
                for p in l {
                    let val_p = self.evaluate_recursive(p, table);
                    val = val.or(val_p);
                }
                val
            }

            To(p, q) => {
                let val_p = self.evaluate_recursive(p, table);
                let val_q = self.evaluate_recursive(q, table);
                val_p.implies(val_q)
            }

            Iff(p, q) => {
                let val_p = self.evaluate_recursive(p, table);
                let val_q = self.evaluate_recursive(q, table);
                val_p.iff(val_q)
            }

            All(..) | Ex(..) => {
                unreachable!("Quantifiers not supported in propositional countermodels")
            }
        };

        // push this evaluation to the table
        table.push(FormulaEvaluation { fml, val });
        val
    }
}

/// Gets a countermodel from a sequent
pub fn get_countermodel(seq: &Sequent) -> CounterModel {
    let mut model = CounterModel::new();
    // collect atoms from the sequent
    for SidedFormula { fml, side } in seq.iter() {
        if let Formula::Pred(id, _) = fml {
            match side {
                Left => {
                    // atoms on the left should be true
                    model.true_atoms.insert(*id);
                }
                Right => {
                    // atoms on the right should be false
                    model.false_atoms.insert(*id);
                }
            }
        }
    }
    model
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::syntax::Formula::*;

    #[test]
    fn test_three_valued_logic() {
        // test AND operation
        assert_eq!(True.and(True), True);
        assert_eq!(True.and(False), False);
        assert_eq!(False.and(True), False);
        assert_eq!(False.and(False), False);
        assert_eq!(True.and(Undefined), Undefined);
        assert_eq!(Undefined.and(True), Undefined);

        // test OR operation
        assert_eq!(True.or(True), True);
        assert_eq!(True.or(False), True);
        assert_eq!(False.or(True), True);
        assert_eq!(False.or(False), False);
        assert_eq!(False.or(Undefined), Undefined);
        assert_eq!(Undefined.or(False), Undefined);

        // test NOT operation
        assert_eq!(True.not(), False);
        assert_eq!(False.not(), True);
        assert_eq!(Undefined.not(), Undefined);
    }

    #[test]
    fn test_countermodel_evaluation() {
        let mut model = CounterModel::new();
        model.true_atoms.insert(0); // P is true (atom id 0)
        model.false_atoms.insert(1); // Q is false (atom id 1)
        // R is undefined (atom id 2)

        assert_eq!(model.get_value(0), ThreeValue::True);
        assert_eq!(model.get_value(1), ThreeValue::False);
        assert_eq!(model.get_value(2), ThreeValue::Undefined);
    }

    #[test]
    fn test_formula_evaluation() {
        let mut model = CounterModel::new();
        model.true_atoms.insert(0); // P is true
        model.true_atoms.insert(1); // Q is true
        model.false_atoms.insert(2); // R is false

        // test P ∧ Q → R (should be False since P∧Q is True but R is False)
        let formula = To(
            Box::new(And(vec![
                Pred(0, vec![]), // P
                Pred(1, vec![]), // Q
            ])),
            Box::new(Pred(2, vec![])), // R
        );

        let truth_table = model.evaluate(&formula);

        // should have evaluations for P, Q, P∧Q, R, and the full formula
        assert!(!truth_table.is_empty());

        // the final result should be False
        let final_evaluation = truth_table.last().unwrap();
        assert_eq!(final_evaluation.val, ThreeValue::False);
    }
}
