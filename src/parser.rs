use pest::iterators::Pairs;
use pest::pratt_parser::PrattParser;
use pest::Parser;
use unicode_normalization::UnicodeNormalization;

#[derive(pest_derive::Parser)]
#[grammar = "parser.pest"]
pub struct FormulaParser;

fn parse_formula(s: &str) {
    let s = s.nfkc().collect::<String>();
    println!("{s}");
}