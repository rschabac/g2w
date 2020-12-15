#[macro_use]
extern crate lalrpop_util;
mod ast;
mod typechecker;

lalrpop_mod!(pub parser); //synthesized by LALRPOP

#[cfg(test)]
mod tests{
	use super::ast;
	use super::parser;
	#[test]
	fn parse_type_test(){
		use ast::{Ty, IntSize, FloatSize};
		let tests = vec![
			("u8", Ty::Int{signed: false, size: IntSize::Size8}),
			("i64", Ty::Int{signed: true, size: IntSize::Size64}),
			("f32", Ty::Float(FloatSize::FSize32)),
			("bool", Ty::Bool),
			("u8 * ", Ty::Ptr(Some(Box::new(Ty::Int{signed: false, size: IntSize::Size8})))),
			("void*", Ty::Ptr(None)),
			("struct\tvector", Ty::Struct(String::from("vector"))),
			("struct vector@<bool>", Ty::GenericStruct{type_var: Box::new(Ty::Bool), name: "vector".to_owned()}),
			("u8 [64]", Ty::Array{length: 64, typ: Box::new(Ty::Int{signed: false, size: IntSize::Size8})}),
			("'\nT\n", Ty::TypeVar(String::from("T"))),
			("'E**", Ty::Ptr(Some(Box::new(Ty::Ptr(Some(Box::new(Ty::TypeVar(String::from("E")))))))))
		];
		let type_parser = parser::TypeParser::new();
		let mut all_succeeded = true;
		for (test_str, expected_parse) in tests {
			match type_parser.parse(test_str) {
				Ok(parse_result) => {
					if parse_result != expected_parse {
						println!("Parse mistake: {:?} parses as {:?}, not {:?}", test_str, parse_result, expected_parse);
						all_succeeded = false;
					}
				},
				Err(error) => {
					println!("Parse error on {:?}: {:?}", test_str, error);
					all_succeeded = false;
				}
			}
		}
		if !all_succeeded {
			panic!();
		}
	}

	#[test]
	fn parse_expr_test(){
		use ast::{Expr, Ty, BinaryOp, UnaryOp};
		let tests = vec![
			("//Comments work\nnull", Expr::LitNull),
			("/*block\tcomments\ntoo*/ true", Expr::LitBool(true)),
			("987", Expr::LitSignedInt(987)),
			("0xA", Expr::LitSignedInt(10)),
			("10u", Expr::LitUnsignedInt(10)),
			("0XFEu", Expr::LitUnsignedInt(254)),
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
				"malloc".to_owned(), 
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
							"f".to_owned(),
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
			),
			("print@<bool>(null)",
				Expr::GenericCall{
					name: "print".to_owned(),
					type_var: Ty::Bool,
					args: vec![
						Expr::LitNull
					]
				}
			)
		];
		let expr_parser = parser::ExprParser::new();
		let mut all_succeeded = true;
		for (test_str, expected_parse) in tests {
			match expr_parser.parse(test_str) {
				Ok(parse_result) => {
					if parse_result != expected_parse {
						println!("Parse mistake: {:?} parses as {:?}, not {:?}", test_str, parse_result, expected_parse);
						all_succeeded = false;
					}
				},
				Err(error) => {
					println!("Parse error on {:?}: {:?}", test_str, error);
					all_succeeded = false;
				}
			}
		}
		if !all_succeeded {
			panic!();
		}
	}

#[test]
	fn parse_stmt_test(){
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
			("f();", Stmt::SCall("f".to_owned(), vec![])),
			("f@<bool>();", Stmt::GenericSCall{
					name: "f".to_owned(),
					type_var: Ty::Bool,
					args: vec![]
				}
			),
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
		let mut all_succeeded = true;
		for (test_str, expected_parse) in tests {
			match stmt_parser.parse(test_str) {
				Ok(parse_result) => {
					if parse_result != expected_parse {
						println!("Parse mistake: {:?} parses as {:?}, not {:?}", test_str, parse_result, expected_parse);
						all_succeeded = false;
					}
				},
				Err(error) => {
					println!("Parse error on {:?}: {:?}", test_str, error);
					all_succeeded = false;
				}
			}
		}
		if !all_succeeded {
			panic!();
		}
	}

	#[test]
	fn parse_gdecl_test(){
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
			("struct a@<erased 'T>{}", Gdecl::GGenericStructDecl{
				name: "a".to_owned(),
				param: "T".to_owned(),
				mode: PolymorphMode::Erased,
				fields: vec![]
			}),
			("void h@<separated 'T>(){}", Gdecl::GGenericFuncDecl{
				ret_type: None,
				name: "h".to_owned(),
				args: vec![],
				body: vec![],
				param: "T".to_owned(),
				mode: PolymorphMode::Separated
			})
		];
		let gdecl_parser = parser::GDeclParser::new();
		let mut all_succeeded = true;
		for (test_str, expected_parse) in tests {
			match gdecl_parser.parse(test_str) {
				Ok(parse_result) => {
					if parse_result != expected_parse {
						println!("Parse mistake: {:?} parses as {:?}, not {:?}", test_str, parse_result, expected_parse);
						all_succeeded = false;
					}
				},
				Err(error) => {
					println!("Parse error on {:?}: {:?}", test_str, error);
					all_succeeded = false;
				}
			}
		}
		if !all_succeeded {
			panic!();
		}
	}

	mod typechecking_tests {
		use crate::typechecker::*;
		use crate::ast::*;
		use crate::ast::Ty::*;
		use super::parser;
		fn setup(expr: &str) -> Result<Ty, String>{
			let (mut ctxt, func_context) = get_empty_localtypecontext();
			return setup_with_localtypecontext_and_funcs(expr, &mut ctxt, &func_context);
		}
		fn setup_with_localtypecontext(expr: &str, ctxt: &mut LocalTypeContext) -> Result<Ty, String>{
			let (_, funcs) = get_empty_localtypecontext();
			return setup_with_localtypecontext_and_funcs(expr, ctxt, &funcs);
		}
		fn setup_with_funcs(expr: &str, funcs: &FuncContext) -> Result<Ty, String>{
			let (mut ctxt, _) = get_empty_localtypecontext();
			return setup_with_localtypecontext_and_funcs(expr, &mut ctxt, funcs);
		}
		fn setup_with_localtypecontext_and_funcs(expr: &str, ctxt: &mut LocalTypeContext, funcs: &FuncContext) -> Result<Ty, String>{
			let expr_parser = parser::ExprParser::new();
			let expr = expr_parser.parse(expr).expect("parse error");
			return typecheck_expr(ctxt, funcs, &expr);
		}
		#[test]
		fn typecheck_expr_test(){
			use std::collections::HashMap;
			assert_eq!(setup("true").unwrap(), Bool);
			assert_eq!(setup("38").unwrap(), Int{signed:true, size: IntSize::Size64});
			assert_eq!(setup("{1, 2, 3}").unwrap(), Array{length: 3, typ: Box::new(Int{signed: true, size: IntSize::Size64})});
			assert_eq!(setup("\"abc\"[{1, 2, 3}[0]]").unwrap(), Int{signed: false, size: IntSize::Size8});
			let mut funcs = HashMap::new();
			let _ = funcs.insert("f".to_owned(), FuncType::NonGeneric{
				args: vec![Bool, Int{signed: true, size: IntSize::Size64}],
				return_type: Some(Struct("abc".to_owned()))
			});
			assert_eq!(setup_with_funcs("f(true, 5)", &funcs).unwrap(), Struct("abc".to_owned()));
			assert!(setup_with_funcs("f@<i32>(true, 5)", &funcs).is_err());
			assert!(setup("cast(u8*, 5)").is_err());
			assert!(setup("f()").is_err());
			assert_eq!(setup("~cast(u8, 4)").unwrap(), Int{signed: false, size: IntSize::Size8});
			assert_eq!(setup("&({1, 2, 3}[0])").unwrap(), Ptr(Some(Box::new(Int{signed: true, size: IntSize::Size64}))));
			assert_eq!(setup("*\"abc\"").unwrap(), Int{signed: false, size: IntSize::Size8});
			assert_eq!(setup("sizeof(bool)").unwrap(), Int{signed: false, size: IntSize::Size64});
			assert!(setup("&true").is_err());
			assert_eq!(setup("8 + 9").unwrap(), Int{signed: true, size: IntSize::Size64});
			assert_eq!(setup("8 + 9").unwrap(), Int{signed: true, size: IntSize::Size64});
			assert!(setup("3.0 + 4").is_err());
			assert_eq!(setup("3 & cast(i32, 1)").unwrap(), Int{signed: true, size: IntSize::Size64});
			assert!(setup("true % 3.4").is_err());
			let mut funcs = HashMap::new();
			let _ = funcs.insert("f".to_owned(), FuncType::Generic{
				args: vec![TypeVar("T".to_owned()), Int{signed: true, size: IntSize::Size64}],
				mode: PolymorphMode::Separated,
				type_var: "T".to_owned(),
				return_type: Some(Struct("abc".to_owned()))
			});
			assert_eq!(setup_with_funcs("f@<bool>(5 == 5, 5)", &funcs).unwrap(), Struct("abc".to_owned()));
			assert!(setup_with_funcs("f(true, 5)", &funcs).is_err());
			assert_eq!(setup("printf(true, 7, 8,8%8,8u,8)").unwrap(), Int{signed:true, size: IntSize::Size32});
			assert!(setup("fprintf(3, 5 + 5u)").is_err());
		}
	}
}

fn main(){
	use std::env::args;
	let expr_parser = parser::ExprParser::new();
	let test_str = &args().collect::<Vec<String>>()[1];
	let parse_result = expr_parser.parse(test_str);
	let (mut empty_localtypecontext, func_context) = typechecker::get_empty_localtypecontext();
	println!("type of '{}' = {:?}", test_str, typechecker::typecheck_expr(&mut empty_localtypecontext, &func_context, &parse_result.unwrap()));
}
