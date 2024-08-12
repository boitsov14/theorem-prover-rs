use crate::lang::Formula;
use crate::new_prover::lang::Side::{Left, Right};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Side {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Cost {
    Alpha,
    Beta(usize),
    Quant,
    Atom,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct FormulaExtended<'a> {
    fml: &'a Formula,
    side: Side,
    cost: Cost,
}

struct SequentExtended<'a> {
    seq: Vec<FormulaExtended<'a>>,
    finished: bool,
}

impl Formula {
    fn get_cost(&self, side: Side) -> Cost {
        use Cost::*;
        use Formula::*;
        use Side::*;
        match (self, side) {
            (Pred(..), _) => Atom,
            (And(_) | Ex(..), Left) | (Or(_) | To(..) | All(..), Right) | (Not(_), _) => Alpha,
            (And(l), Right) | (Or(l), Left) => Beta(l.len()),
            (To(..), Left) | (Iff(..), _) => Beta(2),
            (All(..), Left) | (Ex(..), Right) => Quant,
        }
    }
}
