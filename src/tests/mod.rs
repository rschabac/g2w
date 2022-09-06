mod typechecking_tests {
	use crate::typechecker::*;
	//use crate::ast::*;
	//use crate::ast::Ty::*;
	use crate::ast2::*;
	use crate::ast2::Ty::*;
	use crate::driver::Error;
	fn setup_expr<'src: 'arena, 'arena>(expr: &'src str, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Result<&'arena Ty<'src, 'arena>, Vec<Error>>{
		let (mut ctxt, func_context) = get_empty_localtypecontext();
		setup_expr_with_localtypecontext_and_funcs(expr, &mut ctxt, &func_context, arena, typecache)
	}
	fn setup_expr_with_localtypecontext<'src: 'arena, 'arena: 'ctxt, 'ctxt>(expr: &'src str, ctxt: &'ctxt mut LocalTypeContext<'src, 'arena>, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Result<&'arena Ty<'src, 'arena>, Vec<Error>>{
		let (_, funcs) = get_empty_localtypecontext();
		setup_expr_with_localtypecontext_and_funcs(expr, ctxt, &funcs, arena, typecache)
	}
	fn setup_expr_with_funcs<'src: 'arena, 'arena>(expr: &'src str, funcs: &FuncContext<'src, 'arena>, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Result<&'arena Ty<'src, 'arena>, Vec<Error>>{
		let (mut ctxt, _) = get_empty_localtypecontext();
		setup_expr_with_localtypecontext_and_funcs(expr, &mut ctxt, funcs, arena, typecache)
	}
	fn setup_expr_with_localtypecontext_and_funcs<'src: 'arena, 'arena: 'ctxt, 'ctxt>(expr: &'src str, ctxt: &'ctxt mut LocalTypeContext<'src, 'arena>, funcs: &'ctxt FuncContext<'src, 'arena>, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Result<&'arena Ty<'src, 'arena>, Vec<Error>>{
		use crate::parser::tests::parse_as_expr;
		let mut e: Loc<TypedExpr<'src, 'arena>> = parse_as_expr(expr, arena, typecache)?;
		typecheck_expr(ctxt, funcs, &mut e, typecache)?;
		Ok(e.elt.typ.unwrap())
	}
	#[test]
	fn typecheck_expr_test(){
		use std::collections::HashMap;
		use crate::parser::tests::get_typecache;
		let arena = bumpalo::Bump::new();
		let mut arena_for_typecache = bumpalo::Bump::new();
		let typecache = get_typecache(&mut arena_for_typecache);
		assert_eq!(setup_expr("true", &arena, &typecache).unwrap(), &Bool);
		assert_eq!(setup_expr("38", &arena, &typecache).unwrap(), &Int{signed:true, size: IntSize::Size64});
		//Can't index off of array literals
		//assert_eq!(setup_expr("\"abc\"[{1, 2, 3}[0]]").unwrap(), Int{signed: false, size: IntSize::Size8});
		let (mut ctxt, _) = get_empty_localtypecontext();
		ctxt.locals.insert("x", &Bool);
		assert_eq!(setup_expr_with_localtypecontext("x", &mut ctxt, &arena, &typecache).unwrap(), &Bool);
		let mut funcs = HashMap::new();
		funcs.insert("f", FuncType::NonGeneric{
			args: &[&Bool, &Int{signed: true, size: IntSize::Size64}],
			return_type: Some(&Struct("abc"))
		});
		assert_eq!(setup_expr_with_funcs("f(true, 5)", &funcs, &arena, &typecache).unwrap(), &Struct("abc"));
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f", FuncType::Generic{
			args: &[&Bool, &TypeVar("T")],
			mode: PolymorphMode::Erased,
			type_var: "T",
			return_type: Some(&Struct("abc"))
		});
		assert_eq!(setup_expr_with_funcs("f@<i64>(true, 5)", &funcs, &arena, &typecache).unwrap(), &Struct("abc"));
		assert!(setup_expr("cast(u8*, 5)", &arena, &typecache).is_err());
		assert!(setup_expr("f()", &arena, &typecache).is_err());
		assert_eq!(setup_expr("~cast(u8, 4)", &arena, &typecache).unwrap(), &Int{signed: false, size: IntSize::Size8});
		//assert_eq!(setup_expr("&({1, 2, 3}[0])").unwrap(), Ptr(Some(Box::new(Int{signed: true, size: IntSize::Size64}))));
		assert_eq!(setup_expr("*\"abc\"", &arena, &typecache).unwrap(), &Int{signed: false, size: IntSize::Size8});
		assert_eq!(setup_expr("sizeof(bool)", &arena, &typecache).unwrap(), &Int{signed: false, size: IntSize::Size64});
		assert!(setup_expr("&true", &arena, &typecache).is_err());
		assert_eq!(setup_expr("8 + 9", &arena, &typecache).unwrap(), &Int{signed: true, size: IntSize::Size64});
		assert_eq!(setup_expr("8 + 9", &arena, &typecache).unwrap(), &Int{signed: true, size: IntSize::Size64});
		assert!(setup_expr("3.0 + 4", &arena, &typecache).is_err());
		assert_eq!(setup_expr("3 & 1i32", &arena, &typecache).unwrap(), &Int{signed: true, size: IntSize::Size64});
		assert!(setup_expr("true % 3.4", &arena, &typecache).is_err());
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f", FuncType::Generic{
			args: &[&TypeVar("T"), &Int{signed: true, size: IntSize::Size64}],
			mode: PolymorphMode::Separated,
			type_var: "T",
			return_type: Some(&Struct("abc"))
		});
		assert_eq!(setup_expr_with_funcs("f@<bool>(5 == 5, 5i64)", &funcs, &arena, &typecache).unwrap(), &Struct("abc"));
		assert!(setup_expr_with_funcs("f(true, 5)", &funcs, &arena, &typecache).is_err());
		assert_eq!(setup_expr("printf(\"abc\", 7, 8,8%8,8u64,8)", &arena, &typecache).unwrap(), &Int{signed:true, size: IntSize::Size32});
		assert!(setup_expr("dprintf(3, \"a\", 5 + 5u64)", &arena, &typecache).is_err());
	}
	fn setup_block<'src: 'arena, 'arena>(block: &'src str, expected_ret_ty: Option<&'arena Ty<'src, 'arena>>, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Result<bool, Vec<Error>>{
		let (mut ctxt, func_context) = get_empty_localtypecontext();
		setup_block_with_localtypecontext_and_funcs(block, &mut ctxt, &func_context, expected_ret_ty, arena, typecache)
	}
	fn setup_block_with_localtypecontext<'src: 'arena, 'arena: 'ctxt, 'ctxt>(block: &'src str, ctxt: &'ctxt mut LocalTypeContext<'src, 'arena>, expected_ret_ty: Option<&'arena Ty<'src, 'arena>>, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Result<bool, Vec<Error>>{
		let (_, funcs) = get_empty_localtypecontext();
		setup_block_with_localtypecontext_and_funcs(block, ctxt, &funcs, expected_ret_ty, arena, typecache)
	}
	fn setup_block_with_funcs<'src: 'arena, 'arena>(block: &'src str, funcs: &FuncContext<'src, 'arena>, expected_ret_ty: Option<&'arena Ty<'src, 'arena>>, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Result<bool, Vec<Error>>{
		let (mut ctxt, _) = get_empty_localtypecontext();
		setup_block_with_localtypecontext_and_funcs(block, &mut ctxt, funcs, expected_ret_ty, arena, typecache)
	}
	fn setup_block_with_localtypecontext_and_funcs<'src: 'arena, 'arena: 'ctxt, 'ctxt>(block: &'src str, ctxt: &'ctxt mut LocalTypeContext<'src, 'arena>, funcs: &'ctxt FuncContext<'src, 'arena>, expected_ret_ty: Option<&'arena Ty<'src, 'arena>>, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Result<bool, Vec<Error>>{
		use crate::parser::tests::parse_as_block;
		let mut b: Loc<Block<'src, 'arena>> = parse_as_block(block, arena, typecache)?;
		typecheck_block(ctxt, funcs, &mut b.elt, expected_ret_ty, typecache)
	}
	#[test]
	fn typecheck_block_test(){
		use std::collections::HashMap;
		use crate::parser::tests::get_typecache;
		let arena = bumpalo::Bump::new();
		let mut arena_for_typecache = bumpalo::Bump::new();
		let typecache = get_typecache(&mut arena_for_typecache);
		assert!(!setup_block("{u8 x;}", None, &arena, &typecache).unwrap());
		let (mut ctxt, _) = get_empty_localtypecontext();
		let _ = ctxt.locals.insert("x", &Bool);
		assert!(!setup_block_with_localtypecontext("{x = true;}", &mut ctxt, None, &arena, &typecache).unwrap());
		assert!(setup_block_with_localtypecontext("{bool x;}", &mut ctxt, None, &arena, &typecache).is_err());
		assert!(setup_block("{return;}", None, &arena, &typecache).unwrap());
		assert!(setup_block("{return 3.0;}", Some(&Float(FloatSize::FSize64)), &arena, &typecache).unwrap());
		assert!(setup_block("{return;}", Some(&Bool), &arena, &typecache).is_err());
		assert!(setup_block("{return 3;}", None, &arena, &typecache).is_err());
		assert!(setup_block("{return 3;}", Some(&Bool), &arena, &typecache).is_err());
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f", FuncType::NonGeneric{
			args: &[&Bool, &Int{signed: true, size: IntSize::Size64}],
			return_type: Some(&Struct("abc"))
		});
		assert!(!setup_block_with_funcs("{f(true, 7);}", &funcs, None, &arena, &typecache).unwrap());
		let mut funcs = HashMap::new();
		let _ = funcs.insert("f", FuncType::Generic{
			args: &[&Bool, &TypeVar("T")],
			mode: PolymorphMode::Erased,
			type_var: "T",
			return_type: Some(&Struct("abc"))
		});
		assert!(!setup_block_with_funcs("{f@<i64>(true, 5);}", &funcs, None, &arena, &typecache).unwrap());
		assert!(setup_block("{if true {return true;} else {return false;}}", Some(&Bool), &arena, &typecache).unwrap());
		assert!(!setup_block("{if true {return true;}}", Some(&Bool), &arena, &typecache).unwrap());
		assert!(setup_block("{if 3 {return true;}}", Some(&Bool), &arena, &typecache).is_err());
		assert!(setup_block("{if true {x = 4;}}", None, &arena, &typecache).is_err());
		assert!(!setup_block("{while true {return;}}", None, &arena, &typecache).unwrap());
		assert!(!setup_block("{while true {}}", None, &arena, &typecache).unwrap());
		assert!(setup_block("{while 3 {}}", None, &arena, &typecache).is_err());
	}
	#[test]
	fn typecheck_files_test(){
		use std::fs;
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
			use bumpalo::Bump;
			use bumpalo_herd::Herd;
			use crate::{ast2, driver};
			let mut type_arena = Bump::new();
			use std::sync::{Mutex, RwLock};
			use std::collections::HashMap;
			let typecache = ast2::TypeCache{
				arena: Mutex::new(&mut type_arena),
				cached: RwLock::new(HashMap::new())
			};
			let arena_arena = Herd::new();
			let arena_for_typechecking = arena_arena.get();
			let slice = &[program_source];
			let driver::LexParseResult{ast, errors} = driver::lex_and_parse(slice, &typecache, &arena_arena);
			if !errors.is_empty() {
				println!("{} generated type errors:", path.display());
				for error in errors.iter() {
					println!("{:?}", error);
				}
				panic!();
			}
			let mut sorted_ast: ast2::Program<'_, '_> = ast2::Program::from_gdecls(ast, arena_for_typechecking.as_bump());
			assert!(typecheck_program(&mut sorted_ast, &typecache, &arena_for_typechecking).is_err(), "{} did not create a type error", path.display());
		}
	}
}

#[test]
fn run_file_tests() {
	use crate::{typechecker, driver, frontend};
	use std::fs;
	use rayon::prelude::*;
	let native_target_triple = driver::get_native_target_triple().unwrap();
	let test_file_names: Vec<std::path::PathBuf> = fs::read_dir("src/tests").unwrap()
		.filter_map(|entry| {
			let path: std::path::PathBuf = entry.unwrap().path();
			if path.extension() == Some(std::ffi::OsStr::new("src")) {
				Some(path)
			} else {
				None
			}
		}).collect();
	let mut test_results = Vec::new();
	test_file_names.into_par_iter().map(|test_file_name| -> Result<(), String>{
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
		//let ast: Vec<ast::Gdecl> = program_parser.parse(program_source.as_str()).map_err(|parse_err| format!("parse error in file {}: {}", test_file_name.display(), parse_err))?;
		use bumpalo::Bump;
		use bumpalo_herd::Herd;
		use crate::ast2;
		let mut type_arena = Bump::new();
		use std::sync::{Mutex, RwLock};
		use std::collections::HashMap;
		let typecache = ast2::TypeCache{
			arena: Mutex::new(&mut type_arena),
			cached: RwLock::new(HashMap::new())
		};
		let arena_arena = Herd::new();
		let arena_for_typechecking = arena_arena.get();
		let slice = &[program_source];
		let driver::LexParseResult{ast, errors} = driver::lex_and_parse(slice, &typecache, &arena_arena);
		if !errors.is_empty() {
			return Err(format!("parse errors in file {}: {:?}", test_file_name.display(), errors));
		}
		let mut sorted_ast: ast2::Program<'_, '_> = ast2::Program::from_gdecls(ast, arena_for_typechecking.as_bump());
		let program_context = typechecker::typecheck_program(&mut sorted_ast, &typecache, &arena_for_typechecking).map_err(|type_errs| format!("type errors in file {}: {:?}", test_file_name.display(), type_errs))?;
		let llvm_prog = frontend::cmp_prog(&sorted_ast, &program_context, native_target_triple, "__errno_location", &typecache);
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
	}).collect_into_vec(&mut test_results);
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
		let placeholder_name = std::ffi::OsStr::new("src/tests/temp/placeholder.txt");
		for dir_entry in temp_dir {
			let path = dir_entry.unwrap().path();
			//see placeholder.txt for why this is necessary
			if path != placeholder_name {
				fs::remove_file(path).unwrap();
			}
		}
	}
}
