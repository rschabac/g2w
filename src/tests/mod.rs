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
					println!("Parse mistake: {:?} parses as {}, not {}", test_str, parse_result, expected_parse);
					all_succeeded = false;
				}
			},
			Err(error) => {
				println!("Parse error on {:?}: {}", test_str, error);
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
		("array[5u]", Expr::Index(
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
				println!("Parse error on {:?}: {}", test_str, error);
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
				println!("Parse error on {:?}: {}", test_str, error);
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
				println!("Parse error on {:?}: {}", test_str, error);
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
	fn setup_expr(expr: &str) -> Result<Ty, String>{
		let (mut ctxt, func_context) = get_empty_localtypecontext();
		return setup_expr_with_localtypecontext_and_funcs(expr, &mut ctxt, &func_context);
	}
	fn setup_expr_with_localtypecontext(expr: &str, ctxt: &mut LocalTypeContext) -> Result<Ty, String>{
		let (_, funcs) = get_empty_localtypecontext();
		return setup_expr_with_localtypecontext_and_funcs(expr, ctxt, &funcs);
	}
	fn setup_expr_with_funcs(expr: &str, funcs: &FuncContext) -> Result<Ty, String>{
		let (mut ctxt, _) = get_empty_localtypecontext();
		return setup_expr_with_localtypecontext_and_funcs(expr, &mut ctxt, funcs);
	}
	fn setup_expr_with_localtypecontext_and_funcs(expr: &str, ctxt: &mut LocalTypeContext, funcs: &FuncContext) -> Result<Ty, String>{
		let expr_parser = parser::ExprParser::new();
		let expr = expr_parser.parse(expr).expect("parse error");
		return typecheck_expr(ctxt, funcs, &expr);
	}
	#[test]
	fn typecheck_expr_test(){
		use std::collections::HashMap;
		assert_eq!(setup_expr("true").unwrap(), Bool);
		assert_eq!(setup_expr("38").unwrap(), Int{signed:true, size: IntSize::Size64});
		assert_eq!(setup_expr("{1, 2, 3}").unwrap(), Array{length: 3, typ: Box::new(Int{signed: true, size: IntSize::Size64})});
		//Can't index off of array literals
		//assert_eq!(setup_expr("\"abc\"[{1, 2, 3}[0]]").unwrap(), Int{signed: false, size: IntSize::Size8});
		let (mut ctxt, _) = get_empty_localtypecontext();
		let _ = ctxt.locals.insert("x".to_owned(), Bool);
		assert_eq!(setup_expr_with_localtypecontext("x", &mut ctxt).unwrap(), Bool);
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f".to_owned(), FuncType::NonGeneric{
			args: vec![Bool, Int{signed: true, size: IntSize::Size64}],
			return_type: Some(Struct("abc".to_owned()))
		});
		assert_eq!(setup_expr_with_funcs("f(true, 5)", &funcs).unwrap(), Struct("abc".to_owned()));
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f".to_owned(), FuncType::Generic{
			args: vec![Bool, TypeVar("T".to_owned())],
			mode: PolymorphMode::Erased,
			type_var: "T".to_owned(),
			return_type: Some(Struct("abc".to_owned()))
		});
		assert_eq!(setup_expr_with_funcs("f@<i64>(true, 5)", &funcs).unwrap(), Struct("abc".to_owned()));
		assert!(setup_expr("cast(u8*, 5)").is_err());
		assert!(setup_expr("f()").is_err());
		assert_eq!(setup_expr("~cast(u8, 4)").unwrap(), Int{signed: false, size: IntSize::Size8});
		//assert_eq!(setup_expr("&({1, 2, 3}[0])").unwrap(), Ptr(Some(Box::new(Int{signed: true, size: IntSize::Size64}))));
		assert_eq!(setup_expr("*\"abc\"").unwrap(), Int{signed: false, size: IntSize::Size8});
		assert_eq!(setup_expr("sizeof(bool)").unwrap(), Int{signed: false, size: IntSize::Size64});
		assert!(setup_expr("&true").is_err());
		assert_eq!(setup_expr("8 + 9").unwrap(), Int{signed: true, size: IntSize::Size64});
		assert_eq!(setup_expr("8 + 9").unwrap(), Int{signed: true, size: IntSize::Size64});
		assert!(setup_expr("3.0 + 4").is_err());
		assert_eq!(setup_expr("3 & cast(i32, 1)").unwrap(), Int{signed: true, size: IntSize::Size64});
		assert!(setup_expr("true % 3.4").is_err());
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f".to_owned(), FuncType::Generic{
			args: vec![TypeVar("T".to_owned()), Int{signed: true, size: IntSize::Size64}],
			mode: PolymorphMode::Separated,
			type_var: "T".to_owned(),
			return_type: Some(Struct("abc".to_owned()))
		});
		assert_eq!(setup_expr_with_funcs("f@<bool>(5 == 5, 5)", &funcs).unwrap(), Struct("abc".to_owned()));
		assert!(setup_expr_with_funcs("f(true, 5)", &funcs).is_err());
		assert_eq!(setup_expr("printf(\"abc\", 7, 8,8%8,8u,8)").unwrap(), Int{signed:true, size: IntSize::Size32});
		assert!(setup_expr("fprintf(3, 5 + 5u)").is_err());
	}
	fn setup_stmt(stmt: &str, expected_ret_ty: Option<Ty>) -> Result<bool, String>{
		let (mut ctxt, func_context) = get_empty_localtypecontext();
		return setup_stmt_with_localtypecontext_and_funcs(stmt, &mut ctxt, &func_context, expected_ret_ty);
	}
	fn setup_stmt_with_localtypecontext(stmt: &str, ctxt: &mut LocalTypeContext, expected_ret_ty: Option<Ty>) -> Result<bool, String>{
		let (_, funcs) = get_empty_localtypecontext();
		return setup_stmt_with_localtypecontext_and_funcs(stmt, ctxt, &funcs, expected_ret_ty);
	}
	fn setup_stmt_with_funcs(stmt: &str, funcs: &FuncContext, expected_ret_ty: Option<Ty>) -> Result<bool, String>{
		let (mut ctxt, _) = get_empty_localtypecontext();
		return setup_stmt_with_localtypecontext_and_funcs(stmt, &mut ctxt, funcs, expected_ret_ty);
	}
	fn setup_stmt_with_localtypecontext_and_funcs(stmt: &str, ctxt: &mut LocalTypeContext, funcs: &FuncContext, expected_ret_ty: Option<Ty>) -> Result<bool, String>{
		let stmt_parser = parser::StmtParser::new();
		let stmt = stmt_parser.parse(stmt).expect("parse error");
		return typecheck_stmt(ctxt, funcs, &stmt, &expected_ret_ty);
	}
	#[test]
	fn typecheck_stmt_test(){
		use std::collections::HashMap;
		assert_eq!(setup_stmt("u8 x;", None).unwrap(), false);
		let (mut ctxt, _) = get_empty_localtypecontext();
		let _ = ctxt.locals.insert("x".to_owned(), Bool);
		assert_eq!(setup_stmt_with_localtypecontext("x = true;", &mut ctxt, None).unwrap(), false);
		assert!(setup_stmt_with_localtypecontext("bool x;", &mut ctxt, None).is_err());
		assert_eq!(setup_stmt("return;", None).unwrap(), true);
		assert_eq!(setup_stmt("return 3.0;", Some(Float(FloatSize::FSize64))).unwrap(), true);
		assert!(setup_stmt("return;", Some(Bool)).is_err());
		assert!(setup_stmt("return 3;", None).is_err());
		assert!(setup_stmt("return 3;", Some(Bool)).is_err());
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f".to_owned(), FuncType::NonGeneric{
			args: vec![Bool, Int{signed: true, size: IntSize::Size64}],
			return_type: Some(Struct("abc".to_owned()))
		});
		assert_eq!(setup_stmt_with_funcs("f(true, 7);", &funcs, None).unwrap(), false);
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f".to_owned(), FuncType::Generic{
			args: vec![Bool, TypeVar("T".to_owned())],
			mode: PolymorphMode::Erased,
			type_var: "T".to_owned(),
			return_type: Some(Struct("abc".to_owned()))
		});
		assert_eq!(setup_stmt_with_funcs("f@<i64>(true, 5);", &funcs, None).unwrap(), false);
		assert_eq!(setup_stmt("if true {return true;} else {return false;}", Some(Bool)).unwrap(), true);
		assert_eq!(setup_stmt("if true {return true;}", Some(Bool)).unwrap(), false);
		assert!(setup_stmt("if 3 {return true;}", Some(Bool)).is_err());
		assert!(setup_stmt("if true {x = 4;}", None).is_err());
		assert_eq!(setup_stmt("while true {return;}", None).unwrap(), false);
		assert_eq!(setup_stmt("while true {}", None).unwrap(), false);
		assert!(setup_stmt("while 3 {}", None).is_err());
	}
	#[test]
	fn typecheck_files_test(){
		use std::fs;
		let program_parser = parser::ProgramParser::new();
		for path in fs::read_dir("src/tests/typechecking/should_error").unwrap()
				.filter_map(|entry| {
					//gets only the filenames that end in .src
					let path_buf = entry.unwrap().path();
					if path_buf.extension() == Some(std::ffi::OsStr::new("src")) {
						Some(path_buf)
					} else {
						None
					}
				}){
			let program_source = fs::read_to_string(&path).map_err(|e| format!("io error on {}: {}", path.display(), e.to_string())).unwrap();
			let ast = program_parser.parse(program_source.as_str()).map_err(|e| format!("parse error on {}: {}", path.display(), e.to_string())).unwrap();
			assert!(typecheck_program(&ast).is_err(), "{} did not create a type error", path.display());
		}
	}
}

#[test]
fn run_file_tests() {
	use crate::{typechecker, frontend};
	use super::parser;
	use std::fs;
	let program_parser = parser::ProgramParser::new();
	let test_file_names = fs::read_dir("src/tests").unwrap()
		.filter_map(|entry| {
			let path: std::path::PathBuf = entry.unwrap().path();
			if path.extension() == Some(std::ffi::OsStr::new("src")) {
				Some(path)
			} else {
				None
			}
		});
	let test_results = test_file_names.map(|test_file_name| -> Result<(), String>{
		let program_source = fs::read_to_string(&test_file_name).map_err(|e| format!("io error on {}: {}", test_file_name.display(), e.to_string()))?;
		let mut lines = program_source.split('\n');
		/*
		file must look like:
			/*exit_code
			expected output,
			can be multiple lines
			*/
			actual code
		*/
		let first_line = lines.next().ok_or_else(|| format!("file {} is probably empty", test_file_name.display()))?;
		let should_exit_with: u8 = first_line.strip_prefix("/*")
					.ok_or_else(|| format!("file {} not formatted correctly for testing", test_file_name.display()))?
					.parse().map_err(|_| format!("first line of {} not formatted correctly for testing", test_file_name.display()))?;
		let mut should_print = String::new();
		for line in lines { //just the remaining lines
			if line.starts_with("*/") { break }
			should_print.push_str(line);
			should_print.push('\n');
		}
		let should_print: Vec<u8> = should_print.into();
		let ast: Vec<ast::Gdecl> = program_parser.parse(program_source.as_str()).map_err(|parse_err| format!("parse error in file {}: {}", test_file_name.display(), parse_err))?;
		let program_context = typechecker::typecheck_program(&ast).map_err(|type_err_msg| format!("type error in file {}: {}", test_file_name.display(), type_err_msg))?;
		let llvm_prog = frontend::cmp_prog(&ast.into(), &program_context);
		let mut output_file_name: std::path::PathBuf = test_file_name;
		output_file_name.set_extension("ll");
		use std::ffi::{OsString, OsStr};
		let output_ll_file_name: OsString = [OsStr::new("src"), OsStr::new("tests"), OsStr::new("temp"), output_file_name.file_name().unwrap()].iter().collect::<std::path::PathBuf>().into();
		//write ll prog to output_ll_file_name
		let mut output_ll_file = fs::File::create(&output_ll_file_name).map_err(|io_err| format!("could not create output ll file: {}", io_err))?;
		use std::io::Write;
		write!(output_ll_file, "{}", llvm_prog).unwrap();

		output_file_name.set_extension("exe");
		let output_exe_file_name: OsString = [OsStr::new("src"), OsStr::new("tests"), OsStr::new("temp"), output_file_name.file_name().unwrap()].iter().collect::<std::path::PathBuf>().into();
		//invoke clang
		use std::process::Command;
		let clang_output = Command::new("clang")
					.args([&output_ll_file_name as &OsStr, OsStr::new("-o"), &output_exe_file_name as &OsStr].iter())
					.output().map_err(|io_err| format!("could not call clang: {}", io_err))?;
		if !clang_output.status.success() {
			return Err(format!("clang exited with non-zero status on {}", output_file_name.file_name().unwrap().to_string_lossy()));
		}

		//execute exe file
		let prog_output = Command::new(output_exe_file_name).output().map_err(|io_err| format!("could not execute exe file: {}", io_err))?;
		match prog_output.status.code() {
			None => return Err(format!("{} got signaled", output_file_name.display())),
			Some(code) => if code != should_exit_with as i32 {
				return Err(format!("{} exited with code {}, expected exit code of {}", output_file_name.file_name().unwrap().to_string_lossy(), code, should_exit_with));
			}
		};
		if prog_output.stdout != should_print {
			return Err(format!("{} output does not match expected", output_file_name.file_name().unwrap().to_string_lossy()));
		}
		Ok(())
	});
	let mut total_tests = 0;
	let mut passed_tests = 0;
	let mut cumulative_err_msg = String::new();
	for result in test_results {
		total_tests += 1;
		if let Err(msg) = result {
			cumulative_err_msg.push_str(&msg);
			cumulative_err_msg.push('\n');
		} else {
			passed_tests += 1;
		}
	}
	if !cumulative_err_msg.is_empty() {
		panic!("\n{}/{} file tests passed\n{}", passed_tests, total_tests, cumulative_err_msg);
	} else {
		//delete all ll and exe files in temp, but only if all tests passed
		let temp_dir = fs::read_dir("src/tests/temp").unwrap();
		for dir_entry in temp_dir {
			fs::remove_file(dir_entry.unwrap().path()).unwrap();
		}
	}
}
