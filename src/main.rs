#[macro_use]
extern crate lalrpop_util;
mod ast;
mod typechecker;

lalrpop_mod!(pub parser); //synthesized by LALRPOP

#[cfg(test)]
mod tests{
	use super::ast;
	use super::parser;
	use super::typechecker;
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
			("//Comments work\n\nnull", Expr::LitNull),
			("/*block\tcomments\ntoo*/ true", Expr::LitBool(true)),
			("987", Expr::LitSignedInt(987)),
			("0xA", Expr::LitSignedInt(10)),
			("u10", Expr::LitUnsignedInt(10)),
			("u0XFE", Expr::LitUnsignedInt(254)),
			("\"abc\"", Expr::LitString("abc".to_owned())),
			("my_var", Expr::Id("my_var".to_owned())),
			("{4, null, true}", Expr::LitArr(
				vec![Expr::LitSignedInt(4), Expr::LitNull, Expr::LitBool(true)]
			)),
			("array[u5]", Expr::Index(
				Box::new(Expr::Id("array".to_owned())),
				Box::new(Expr::LitUnsignedInt(5))
			)),
			("point.x", Expr::Proj(Box::new(Expr::Id("point".to_owned())), "x".to_owned())),
			("malloc(64)", Expr::Call(
				Box::new(Expr::Id("malloc".to_owned())), 
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
			("sizeof (struct vector) ", Expr::Sizeof(Ty::Struct("vector".to_owned()))),
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
							Box::new(Expr::Id("f".to_owned())),
							vec![
								Expr::Cast(
									Ty::Ptr(Some(Box::new(
										Ty::Int{signed: false, size: ast::IntSize::Size8}
									))),
									Box::new(Expr::Id("x".to_owned()))
								),
								Expr::LitArr(vec![
									Expr::Proj(
										Box::new(Expr::Id("a".to_owned())),
										"x".to_owned()
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

#[test]
	fn parse_Stmt_test(){
		use ast::{Ty, Expr, Stmt};
		let tests = vec![
			("x = 4;", Stmt::Assign(
				Expr::Id("x".to_owned()),
				Expr::LitSignedInt(4)
			)),
			("bool b;", Stmt::Decl(
				Ty::Bool,
				"b".to_owned()
			)),
			("return;", Stmt::Return(None)),
			("return null;", Stmt::Return(Some(Expr::LitNull))),
			("x;", Stmt::BareExpr(Expr::Id("x".to_owned()))),
			("while true { x = 4; }", Stmt::While(Expr::LitBool(true), vec![
				Stmt::Assign(Expr::Id("x".to_owned()), Expr::LitSignedInt(4))
			])),
			("if true { return; }", Stmt::If(Expr::LitBool(true),
				vec![
					Stmt::Return(None)
				],
				vec![]
			)),
			("if true{return;}else{x=y;}", Stmt::If(Expr::LitBool(true),
				vec![
					Stmt::Return(None)
				],
				vec![
					Stmt::Assign(Expr::Id("x".to_owned()), Expr::Id("y".to_owned()))
				]
			)),
			("if true{return;}else if false{}else{x=y;}", Stmt::If(Expr::LitBool(true),
				vec![
					Stmt::Return(None)
				],
				vec![
					Stmt::If(Expr::LitBool(false),
						vec![],
						vec![
							Stmt::Assign(Expr::Id("x".to_owned()), Expr::Id("y".to_owned()))
						]
					)
				]
			)),
				
		];
		let stmt_parser = parser::StmtParser::new();
		let mut allSucceeded = true;
		for (test_str, expectedParse) in tests {
			match stmt_parser.parse(test_str) {
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
	fn parse_GDecl_test(){
		use ast::{Gdecl, Ty, PolymorphMode};
		let tests = vec![
			("bool x;", Gdecl::GVarDecl(Ty::Bool, "x".to_owned())),
			("bool f(){return;}", Gdecl::GFuncDecl{
				ret_type: Some(Ty::Bool),
				name: "f".to_owned(),
				args: vec![],
				body: vec![
						ast::Stmt::Return(None)
					]
			}),
			("void g(bool x, bool y){}", Gdecl::GFuncDecl{
				ret_type: None,
				name: "g".to_owned(),
				args: vec![
					(Ty::Bool, "x".to_owned()),
					(Ty::Bool, "y".to_owned())
					],
				body: vec![]
			}),
			("struct a{bool x;bool y;}", Gdecl::GStructDecl{
				name: "a".to_owned(),
				fields: vec![
					(Ty::Bool, "x".to_owned()),
					(Ty::Bool, "y".to_owned())
				]
			}),
			("struct a<erased 'T>{}", Gdecl::GGenericStructDecl{
				name: "a".to_owned(),
				param: "T".to_owned(),
				mode: PolymorphMode::Erased,
				fields: vec![]
			}),
			("void h<separated 'T>(){}", Gdecl::GGenericFuncDecl{
				ret_type: None,
				name: "h".to_owned(),
				args: vec![],
				body: vec![],
				param: "T".to_owned(),
				mode: PolymorphMode::Separated
			})
		];
		let gdecl_parser = parser::GDeclParser::new();
		let mut allSucceeded = true;
		for (test_str, expectedParse) in tests {
			match gdecl_parser.parse(test_str) {
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

	mod typechecking_tests {
		use crate::typechecker::*;
		use crate::ast::*;
		use crate::ast::Ty::*;
		use super::parser;
		#[test]
		fn typecheck_expr_test1(){
			let mut empty_typecontext = get_empty_typecontext();
			let expr_parser = parser::ExprParser::new();
			let expr = expr_parser.parse("true").expect("parse error");
			let typecheck_result = typecheck_expr(&mut empty_typecontext, &expr);
			assert_eq!(typecheck_result.unwrap(), Bool);
		}
		#[test]
		fn typecheck_expr_test2(){
			let mut empty_typecontext = get_empty_typecontext();
			let expr_parser = parser::ExprParser::new();
			let expr = expr_parser.parse("38").expect("parse error");
			let typecheck_result = typecheck_expr(&mut empty_typecontext, &expr);
			assert_eq!(typecheck_result.unwrap(), Int{signed:true, size: IntSize::Size64});
		}
		#[test]
		fn typecheck_expr_test3(){
			let mut empty_typecontext = get_empty_typecontext();
			let expr_parser = parser::ExprParser::new();
			let expr = expr_parser.parse("{1, 2, 3}").expect("parse error");
			let typecheck_result = typecheck_expr(&mut empty_typecontext, &expr);
			assert_eq!(typecheck_result.unwrap(), Array{length: 3, typ: Box::new(Int{signed: true, size: IntSize::Size64})});
		}
		#[test]
		fn typecheck_expr_test4(){
			let mut empty_typecontext = get_empty_typecontext();
			let expr_parser = parser::ExprParser::new();
			let expr = expr_parser.parse("\"abc\"[{1, 2, 3}[0]]").expect("parse error");
			let typecheck_result = typecheck_expr(&mut empty_typecontext, &expr);
			assert_eq!(typecheck_result.unwrap(), Int{signed: false, size: IntSize::Size8});
		}
	}
}

fn main(){
	use std::env::args;
	let expr_parser = parser::ExprParser::new();
	let test_str = &args().collect::<Vec<String>>()[1];
	let parse_result = expr_parser.parse(test_str);
	let mut empty_typecontext = typechecker::get_empty_typecontext();
	println!("type of '{}' = {:?}", test_str, typechecker::typecheck_expr(&mut empty_typecontext, &parse_result.unwrap()));
}
