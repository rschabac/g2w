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
		("u8 * ", Ty::Ptr(Some(Box::new(Ty::Int{signed: false, size: IntSize::Size8})))),
		("void*", Ty::Ptr(None)),
		("struct\tvector", Ty::Struct(String::from("vector"))),
		("u8 [64]", Ty::Array{length: 64, typ: Box::new(Ty::Int{signed: false, size: IntSize::Size8})}),
		("'\nT\n", Ty::TypeVar(String::from("T"))),
		("'E**", Ty::Ptr(Some(Box::new(Ty::Ptr(Some(Box::new(Ty::TypeVar(String::from("E")))))))))
	];
	let type_parser = parser::TypeParser::new();
	let mut allSucceeded = true;
	for (test_str, expectedParse) in tests {
		match type_parser.parse(test_str) {
			Ok(parseResult) => {
				if parseResult != expectedParse {
					println!("Parse mistake: {:?} parses as {:?}, not {:?}", test_str, parseResult, expectedParse);
					allSucceeded = false;
				}
			},
			Err(error) => {
				println!("Parse error on {:?}: {:?}", test_str, error);
				allSucceeded = false;
			}
		}
	}
	if !allSucceeded {
		panic!();
	}
}

#[test]
fn parse_Expr_test(){
	use ast::{Expr, Ty, BinaryOp, UnaryOp};
	let tests = vec![
		("null", Expr::LitNull),
		("true", Expr::LitBool(true)),
		("987", Expr::LitSignedInt(987)),
		("0xA", Expr::LitSignedInt(10)),
		("u10", Expr::LitUnsignedInt(10)),
		("u0XFE", Expr::LitUnsignedInt(254)),
		("\"abc\"", Expr::LitString("abc".to_string())),
		("my_var", Expr::Id("my_var".to_string())),
		("{4, null, true}", Expr::LitArr(
			vec![Expr::LitSignedInt(4), Expr::LitNull, Expr::LitBool(true)]
		)),
		("array[u5]", Expr::Index(
			Box::new(Expr::Id("array".to_string())),
			Box::new(Expr::LitUnsignedInt(5))
		)),
		("point.x", Expr::Proj(Box::new(Expr::Id("point".to_string())), "x".to_string())),
		("malloc(64)", Expr::Call(
			Box::new(Expr::Id("malloc".to_string())), 
			vec![Expr::LitSignedInt(64)]
		)),
		("cast(u8,null)", Expr::Cast(
			Ty::Int{signed:false, size: ast::IntSize::Size8},
			Box::new(Expr::LitNull)
		)),
		("8 + 8", Expr::Binop(
			Box::new(Expr::LitSignedInt(8)),
			BinaryOp::Add,
			Box::new(Expr::LitSignedInt(8)),
		)),
		("~ true", Expr::Unop(
			UnaryOp::Bitnot,
			Box::new(Expr::LitBool(true))
		)),
		("&false", Expr::GetRef(Box::new(Expr::LitBool(false)))),
		("*null", Expr::Deref(Box::new(Expr::LitNull))),
		("sizeof (struct vector) ", Expr::Sizeof(Ty::Struct("vector".to_string()))),
		("null*null+null", Expr::Binop(
			Box::new(Expr::Binop(
				Box::new(Expr::LitNull),
				BinaryOp::Mul,
				Box::new(Expr::LitNull)
			)),
			BinaryOp::Add,
			Box::new(Expr::LitNull)
		)),
		("!f(cast(u8*, x), {a.x, ~{null}}) + 1",
			Expr::Binop(
				Box::new(Expr::Unop(
					UnaryOp::Lognot,
					Box::new(Expr::Call(
						Box::new(Expr::Id("f".to_string())),
						vec![
							Expr::Cast(
								Ty::Ptr(Some(Box::new(
									Ty::Int{signed: false, size: ast::IntSize::Size8}
								))),
								Box::new(Expr::Id("x".to_string()))
							),
							Expr::LitArr(vec![
								Expr::Proj(
									Box::new(Expr::Id("a".to_string())),
									"x".to_string()
								),
								Expr::Unop(
									UnaryOp::Bitnot,
									Box::new(Expr::LitArr(vec![
										Expr::LitNull
									]))
								)
							])
						]
					))
				)),
				BinaryOp::Add,
				Box::new(Expr::LitSignedInt(1))
			)
		)

	];
	let expr_parser = parser::ExprParser::new();
	let mut allSucceeded = true;
	for (test_str, expectedParse) in tests {
		match expr_parser.parse(test_str) {
			Ok(parseResult) => {
				if parseResult != expectedParse {
					println!("Parse mistake: {:?} parses as {:?}, not {:?}", test_str, parseResult, expectedParse);
					allSucceeded = false;
				}
			},
			Err(error) => {
				println!("Parse error on {:?}: {:?}", test_str, error);
				allSucceeded = false;
			}
		}
	}
	if !allSucceeded {
		panic!();
	}
}

fn main() {
	let expr_parser = parser::ExprParser::new();
	let parse_result = expr_parser.parse("7d9s9");
	println!("{:?}", parse_result);
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
