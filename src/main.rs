#[macro_use]
extern crate lalrpop_util;
mod ast;
mod typechecker;

lalrpop_mod!(pub parser); //synthesized by LALRPOP

#[cfg(test)]
mod tests;

fn main() -> Result<(), String>{
	use std::env::args;
	use std::fs::read_to_string;
	let program_parser = parser::ProgramParser::new();
	let filename = &args().collect::<Vec<String>>()[1];
	let program_source = read_to_string(filename).map_err(|e| format!("io error: {}", e.to_string()))?;
	let ast = program_parser.parse(program_source.as_str()).unwrap();
	typechecker::typecheck_program(ast)
}
