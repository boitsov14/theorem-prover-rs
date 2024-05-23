mod formula;
mod naming;
mod parser;
mod prover;
mod unification;

pub use crate::parser::{modify_tptp, parse};
pub use crate::prover::{example, example_iltp_prop};
use paste::paste;

// TODO: 2024/05/24 独立させる
#[macro_export]
macro_rules! test {
    ($func:ident, $idx:expr, $($arg:expr),*) => {
        paste! {
            #[test]
            fn [<test_ $func _ $idx>]() {
                $func($($arg),*);
            }
        }
    }
}
