mod formula;
mod parser;

use crate::parser::parse;

fn main() {
    println!("Hello, world!");
    let s = "P and Q";
    let Some((fml, inf)) = parse(s) else {
        return;
    };
    println!("{}", fml.to_str_inf(&inf));
}
