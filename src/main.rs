#[macro_use]
extern crate lalrpop_util;
mod ast;

lalrpop_mod!(pub parser); // synthesized by LALRPOP

#[test]
fn parse_Type_test(){
	use ast::{Ty, IntSize, FloatSize};
	let tests = vec![
		("u8", Ty::Int{signed: false, size: IntSize::Size8}),
		("i64", Ty::Int{signed: true, size: IntSize::Size64}),
		("f32", Ty::Float(FloatSize::FSize32)),
		("bool", Ty::Bool),
		("u8 * ", Ty::Ptr(Box::new(Some(Ty::Int{signed: false, size: IntSize::Size8})))),
		("void*", Ty::Ptr(Box::new(None))),
		("struct\tvector", Ty::Struct(String::from("vector"))),
		("'\nT\n", Ty::TypeVar(String::from("T")))
	];
	let type_parser = parser::TypeParser::new();
	for (test_str, expectedParse) in tests{
		assert!(type_parser.parse(test_str).unwrap() == expectedParse);
	}
}

fn main() {
	parse_Type_test();
}

/*
#[test]
fn calculator1() {
	assert!(calculator1::TermParser::new().parse("22").is_ok());
		assert!(calculator1::TermParser::new().parse("(22)").is_ok());
			assert!(calculator1::TermParser::new().parse("((((22))))").is_ok());
				assert!(calculator1::TermParser::new().parse("((22)").is_err());
}
*/
