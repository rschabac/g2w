#[macro_use]
extern crate lalrpop_util;

///Handles parsing command-line arguments, reading input files, invoking clang, and generating output files
mod driver;
///Data structures that represent a parsed input file
mod ast;
///Checks the program for type errors
mod typechecker;
///generates a representation of an llvm program
mod frontend;
///Data structures that represent an llvm program
mod llvm;
///Turns source text into a stream of lists of tokens
mod lexer;
///Turns a list of tokens into an ast2
mod parser;

#[allow(dead_code)] //TODO: remove this later
mod ast2;

#[cfg(test)]
mod tests;

lalrpop_mod!(
	#[doc(hidden)]	//don't include generated parser code in documentation
	#[allow(clippy::all)] //This seems to prevent clippy from checking the generated parser file
	pub oldparser
);

///Just calls [driver::print_timings], does nothing else.
///
///If any error is encountered, it will be printed to standard error.
fn main() -> Result<(), String> {
	driver::print_timings()
}
