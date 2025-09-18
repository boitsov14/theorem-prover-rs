use crate::{
    core::{names::Names, syntax::Formula},
    prover::sequent::{Sequent, Side::*, SidedFormula},
};
use ThreeValue::*;
use rustc_hash::FxHashSet;
use std::{fmt, fs::File, io::Write, path::PathBuf, vec};

/// Three-valued logic
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ThreeValue {
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

    const fn iff(self, other: Self) -> Self {
        // p ↔ q is equivalent to (p → q) ∧ (q → p)
        self.implies(other).and(other.implies(self))
    }
}

impl fmt::Display for ThreeValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            True => write!(f, "T"),
            False => write!(f, "F"),
            Undefined => write!(f, "-"),
        }
    }
}

/// A pair of formula and its evaluation result
#[derive(Clone, Debug)]
pub struct FormulaEvaluation<'a> {
    /// Formula being evaluated
    fml: &'a Formula,
    /// Evaluation result
    val: ThreeValue,
}

/// Countermodel representing truth assignments for atoms
#[derive(Clone, Debug)]
pub struct CounterModel {
    /// Left side atoms
    true_atoms: FxHashSet<usize>,
    /// Right side atoms
    false_atoms: FxHashSet<usize>,
}

impl CounterModel {
    /// Creates a new countermodel from a sequent
    pub fn new(seq: &Sequent) -> Self {
        let mut model = Self {
            true_atoms: FxHashSet::default(),
            false_atoms: FxHashSet::default(),
        };
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

    /// Gets the three-valued logic value for an atom
    fn get_value(&self, atom: usize) -> ThreeValue {
        if self.true_atoms.contains(&atom) {
            ThreeValue::True
        } else if self.false_atoms.contains(&atom) {
            ThreeValue::False
        } else {
            ThreeValue::Undefined
        }
    }

    /// Evaluates a sequent and creates a truth table, showing all subformula evaluations
    /// Left-side formulas should evaluate to True, right-side formulas should evaluate to False
    pub fn evaluate<'a>(&self, seq: &'a Sequent) -> Vec<FormulaEvaluation<'a>> {
        let mut table = vec![];

        for SidedFormula { fml, side } in seq.iter() {
            // evaluate the formula
            let val = self.evaluate_recursive(fml, &mut table);
            assert_eq!(
                val,
                match side {
                    Left => ThreeValue::True,
                    Right => ThreeValue::False,
                },
                "Countermodel evaluation failed"
            );
        }
        table
    }

    /// Recursively evaluates a formula and fills the truth table
    fn evaluate_recursive<'a>(
        &self,
        fml: &'a Formula,
        table: &mut Vec<FormulaEvaluation<'a>>,
    ) -> ThreeValue {
        use Formula::*;

        // check if this formula is already evaluated
        for FormulaEvaluation { fml: fml0, val } in table.iter() {
            if fml == *fml0 {
                return *val;
            }
        }

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

/// Generates LaTeX table for countermodel truth table
pub fn generate_latex(seq: &Sequent, names: &Names, table: &[FormulaEvaluation], out: &str) {
    // prepare formula row and value row
    let mut fmls = vec![];
    let mut vals = vec![];

    for FormulaEvaluation { fml, val } in table {
        fmls.push(format!("${}$", fml.display(names)));
        vals.push(val.to_string());
    }

    // add the overall sequent evaluation (should be False)
    fmls.push(format!("${}$", seq.display(names)));
    vals.push(False.to_string());

    // create column specification
    // centered columns with vertical lines
    let spec = "|c".repeat(table.len() + 1) + "|";

    // join rows with & separator
    let fmls = fmls.join(" & ");
    let vals = vals.join(" & ");

    // embed proof into LaTeX template
    let table = include_str!("../../templates/countermodel.tex")
        .replace("SPEC", &spec)
        .replace("FMLS", &fmls)
        .replace("VALS", &vals);

    // save LaTeX file
    let mut file = File::create(PathBuf::from(out).join("countermodel.tex")).unwrap();
    file.write_all(table.as_bytes()).unwrap();
}
