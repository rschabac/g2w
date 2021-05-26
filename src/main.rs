#[macro_use]
extern crate lalrpop_util;
mod ast;
mod typechecker;
mod llvm;

#[allow(dead_code)] //TODO: remove this later
mod frontend;

//This seems to prevent clippy from checking the generated parser file
lalrpop_mod!(#[allow(clippy::all)] pub parser);

#[cfg(test)]
mod tests;

fn main() -> Result<(), String>{
	use std::env::args;
	let program_parser = parser::ProgramParser::new();
	let argv: Vec<String> = args().collect();
	let mut program_source = String::new();
	if argv.len() == 1 {
		//read source from stdin
		use std::io::{self, Read};
		let mut stdin = io::stdin();
		stdin.read_to_string(&mut program_source).map_err(|e|
			format!("io error: {}", e))?;
	} else {
		//read source from file given as argument
		let filename = &argv[1];
		program_source = std::fs::read_to_string(filename).map_err(|e| format!("io error: {}", e))?;
	}
	let ast: Vec<ast::Gdecl> = program_parser.parse(program_source.as_str()).unwrap();
	let program_context = typechecker::typecheck_program(&ast).map_err(|err_msg| {
		let mut result = "Type Error: ".to_owned();
		result.push_str(err_msg.as_str());
		result
	})?;
	let llvm_prog = frontend::cmp_prog(&ast.into(), &program_context);
	let mut output_file = std::fs::File::create("./output.ll").map_err(|e| format!("could not open output file: {}", e))?;
	use std::io::Write;
	write!(output_file, "{}", llvm_prog).map_err(|e| format!("io error: {}", e))?;
	Ok(())
}
