use crate::lang::Formula;

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
