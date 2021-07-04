use crate::ast;
use std::collections::{HashMap, HashSet};

pub enum FuncType{
	NonGeneric{return_type: Option<ast::Ty>, args: Vec<ast::Ty>},
	Generic{return_type: Option<ast::Ty>, mode: ast::PolymorphMode, type_var: String, args: Vec<ast::Ty>}
}
pub enum StructType{
	NonGeneric(Vec<(String, ast::Ty)>),
	Generic{mode: ast::PolymorphMode, type_var: String, fields: Vec<(String, ast::Ty)>}
}

type LocalContext = HashMap<String, ast::Ty>;
type GlobalContext = HashMap<String, ast::Ty>;
//type StructContext = HashMap<String, Vec<(String, ast::Ty)>>;
pub type StructContext = HashMap<String, StructType>;

//FuncContext contains generic and non-generic functions
//a generic and non-generic function cannot share the same name
pub type FuncContext = HashMap<String, FuncType>;

pub struct LocalTypeContext{
	pub locals: LocalContext,
	pub globals: GlobalContext,
	pub structs: StructContext,
	pub type_for_lit_nulls: Option<ast::Ty>,
	pub type_var: Option<(String, ast::PolymorphMode)>,
	pub is_lhs: bool,
}

pub fn get_empty_localtypecontext() -> (LocalTypeContext, FuncContext) {
	(LocalTypeContext{
		locals: HashMap::new(),
		globals: HashMap::new(),
		structs: HashMap::new(),
		type_for_lit_nulls: None,
		type_var: None,
		is_lhs: false
	},
	HashMap::new())
}

pub fn replace_type_var_with(original: ast::Ty, type_var_str: &str, replacement: &ast::Ty) -> ast::Ty {
	use ast::Ty::*;
	match original {
		TypeVar(s) => {
			if s == type_var_str {
				replacement.clone()
			} else {
				panic!("when replacing '{}, found other type var, '{}", type_var_str, s);
			}
		},
		Ptr(Some(t)) => {
			let replaced = replace_type_var_with(*t, type_var_str, replacement);
			Ptr(Some(Box::new(replaced)))
		}
		Array{typ, length} => {
			let replaced = replace_type_var_with(*typ, type_var_str, replacement);
			Array{typ: Box::new(replaced), length}
		}
		GenericStruct{type_var, name} => {
			let replaced = replace_type_var_with(*type_var, type_var_str, replacement);
			GenericStruct{type_var: Box::new(replaced), name}
		}
		Bool | Int{..} | Float(_) | Struct(_) | Ptr(None) => original
	}
}

//This function is called on all types that appear in the ast, and makes sure that any struct names
//are used appropriately, and that no erased type vars are passed to a separated struct or a
//separated function.
fn all_struct_names_valid(t: &ast::Ty, struct_context: &StructContext, current_type_var: &Option<(String, ast::PolymorphMode)>) -> Result<(), String> {
	use ast::Ty::*;
	use StructType::*;
	match t {
	Struct(s) => match struct_context.get(s) {
		None => Err(format!("struct {} does not exist", s)),
		Some(Generic{..}) => Err(format!("struct {} is generic", s)),
		Some(NonGeneric(_)) => Ok(())
	},
	GenericStruct{name, type_var: type_param} => match struct_context.get(name) {
		None => Err(format!("struct {} does not exist", name)),
		Some(NonGeneric(_)) => Err(format!("struct {} is not generic", name)),
		Some(Generic{mode, ..}) => {
			let type_var_in_param = type_param.recursively_find_type_var();
			match (type_var_in_param, current_type_var) {
				//cannot use the type struct A@<'T> in a non-generic function/struct definition
				(Some(s), None) => {
					return Err(format!("Cannot pass unknown type variable '{} to struct {}", s, name));
				},
				(Some(s), Some((current_var, current_mode))) => {
					//cannot use the type struct A@<'T> if 'T is not the current type var
					if current_var.as_str() != s {
						return Err(format!("Cannot pass unknown type variable '{} to struct {}", current_var, name));
					}
					//cannot pass an erased type var to a separated struct
					if *current_mode == ast::PolymorphMode::Erased && *mode == ast::PolymorphMode::Separated {
						return Err(format!("Cannot pass erased type variable '{} to separated struct {}", s, name));
					}
				}
				_ => ()
			};
			all_struct_names_valid(type_param, struct_context, current_type_var)
		}
	},
	Ptr(Some(t)) | Array{typ: t, ..} => all_struct_names_valid(t, struct_context, current_type_var),
	_ => Ok(())
	}
}

//when typechecking a function call, it the function is one of these, the
//number and type of arguments are not checked (each individual argument must
//still be well-typed though).
pub static PRINTF_FAMILY: &[&str] = &[
	"printf",
	"sprintf",
	//"fprintf", //this requires a FILE*, which will require c header files to define
	"snprintf",
	"dprintf"
];

fn typecheck_printf(func_name: &str, args: &[ast::Expr], ctxt: &mut LocalTypeContext, funcs: &FuncContext) -> Result<(), String> {
	/*
	According to the C standard, there is something called "default argument promotion" that happens when the expected type
	of the argument is unknown (such as when passing arguments to printf). This means that floats are converted to doubles,
	and chars, shorts, and enums are converted to int (probably int, maybe even long). Ideally, I could do this myself in
	the frontend, but for now, I will just give an error when the arguments to printf are one of these shorter types.
	*/
	use ast::Ty::*;
	use ast::IntSize::*;
	use ast::FloatSize::*;
	if args.is_empty() {
		return Err("printf requires at least one argument".to_owned());
	}
	let starting_index: usize; //index of first variadic param in args
	match func_name {
		"printf" => {
			if typecheck_expr(ctxt, funcs, &args[0])? != Ptr(Some(Box::new(Int{size: Size8, signed: false}))) {
				return Err("first argument to printf must be a u8*".to_owned());
			}
			starting_index = 1;
		},
		"sprintf" => {
			if args.len() < 2 {
				return Err("sprintf requires at least 2 arguments".to_owned());
			}
			if typecheck_expr(ctxt, funcs, &args[0])? != Ptr(Some(Box::new(Int{size: Size8, signed: false}))) {
				return Err("first argument to sprintf must be a u8*".to_owned());
			}
			if typecheck_expr(ctxt, funcs, &args[1])? != Ptr(Some(Box::new(Int{size: Size8, signed: false}))) {
				return Err("second argument to sprintf must be a u8*".to_owned());
			}
			starting_index = 2;
		},
		"snprintf" => {
			if args.len() < 3 {
				return Err("snprintf requires at least 3 arguments".to_owned());
			}
			if typecheck_expr(ctxt, funcs, &args[0])? != Ptr(Some(Box::new(Int{size: Size8, signed: false}))) {
				return Err("first argument to snprintf must be a u8*".to_owned());
			}
			if typecheck_expr(ctxt, funcs, &args[1])? != (Int{size: Size64, signed: false}) {
				return Err("second argument to snprintf must be a u64".to_owned());
			}
			if typecheck_expr(ctxt, funcs, &args[2])? != Ptr(Some(Box::new(Int{size: Size8, signed: false}))) {
				return Err("third argument to snprintf must be a u8*".to_owned());
			}
			starting_index = 3;
		},
		"dprintf" => {
			if args.len() < 2 {
				return Err("dprintf requires at least 2 arguments".to_owned());
			}
			if typecheck_expr(ctxt, funcs, &args[1])? != (Int{size: Size32, signed: true}){
				return Err("first argument to dprintf must be a i32".to_owned());
			}
			if typecheck_expr(ctxt, funcs, &args[1])? != Ptr(Some(Box::new(Int{size: Size8, signed: false}))) {
				return Err("second argument to dprintf must be a u8*".to_owned());
			}
			starting_index = 2;
		},
		_ => panic!("typecheck_printf called with non-printf function {} (maybe it's just not in PRINT_FAMILY)", func_name)
	};
	for (i, e) in args[starting_index..].iter().enumerate() {
		let correction: Option<(&str, &str)> = match typecheck_expr(ctxt, funcs, e)? {
			Float(FSize32) => Some(("f32", "f64")),
			Int{size: Size8, signed: true} => Some(("i8", "i32")),
			Int{size: Size8, signed: false} => Some(("u8", "u32")),
			Int{size: Size16, signed: true} => Some(("i16", "i32")),
			Int{size: Size16, signed: false} => Some(("u16", "u32")),
			_ => None
		};
		if let Some((bad, good)) = correction {
			return Err(format!("{} argument {} must be manually promoted from {} to {}", func_name, i + starting_index + 1, bad, good));
		}
	};
	Ok(())
}

pub fn typecheck_expr(ctxt: &mut LocalTypeContext, funcs: &FuncContext, e: &ast::Expr) -> Result<ast::Ty, String>{
use ast::Ty::*;
use ast::Expr::*;
use ast::IntSize::*;
match e {
	LitNull => match &mut ctxt.type_for_lit_nulls {
		Some(t @ Ptr(_)) => Ok(t.clone()),
		Some(t) => Err(format!("Cannot make null literal have type {}", t)),
		None => Err("Cannot infer type of null literal".to_owned())
	},
	LitBool(_) => Ok(Bool),
	LitSignedInt(_) => Ok(Int{signed: true, size: Size64}),
	LitUnsignedInt(_) => Ok(Int{signed: false, size: Size64}),
	LitFloat(_) => Ok(Float(ast::FloatSize::FSize64)),
	LitString(_) => Ok(Ptr(Some(Box::new(Int{signed:false, size: Size8})))),
	Id(var) => match ctxt.locals.get(var) {
			Some(t) => Ok(t.clone()),
			None => match ctxt.globals.get(var) {
				Some(t) => Ok(t.clone()),
				None => Err(format!("undeclared variable {}", var))
		}
	},
	Index(base, index) => {
		ctxt.type_for_lit_nulls = None;
		let base_typ = typecheck_expr(ctxt, funcs, base)?;
		let result_type = match base_typ {
			Ptr(Some(typ)) => Ok(*typ),
			Array{typ, ..} =>
				if !matches!(base as &ast::Expr, ast::Expr::Id(_) | ast::Expr::Index(_,_) | ast::Expr::Proj(_,_) | ast::Expr::Deref(_)) {
					Err("Cannot index off of something of array type that is not an lvalue".to_owned())
				} else {
					Ok(*typ)
				},
			Ptr(None) => Err("Can't index off of a void*".to_owned()),
			_ => Err(format!("{} is not an array or pointer", base_typ))
		};
		let result_type = result_type?;
		let index_typ = typecheck_expr(ctxt, funcs, index)?;
		match index_typ {
			Int{..} => Ok(result_type),
			_ => Err(format!("Array indices must be integers, not {}", index_typ))
		}
	},
	Proj(base, field) => {
		use StructType::*;
		//if base is LitNull, I can't determine what struct it is
		ctxt.type_for_lit_nulls = None;
		let base_typ = typecheck_expr(ctxt, funcs, base)?;
		match base_typ {
			Ptr(Some(ref boxed)) => match boxed as &ast::Ty {
				Struct(struct_name) => match ctxt.structs.get(struct_name) {
					None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
					Some(NonGeneric(field_list)) => {
						for (field_name, typ) in field_list.iter() {
							if field.eq(field_name) {
								return Ok(typ.clone());
							}
						}
						Err(format!("struct {} does not have a {} field", struct_name, field))
					},
					Some(Generic{..}) => panic!("Proj: base had type {}, but struct context contained a generic struct for {}", base_typ, struct_name)
				},
				GenericStruct{type_var: ref type_param, name: ref struct_name} => match ctxt.structs.get(struct_name) {
					None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
					Some(NonGeneric(_)) => panic!("Proj: base had type {}, but struct context contained a non-generic struct for {}", base_typ, struct_name),
					Some(Generic{mode: _, type_var, fields}) => {
						for (field_name, typ) in fields.iter() {
							if field.eq(field_name) {
								let replaced_ty = replace_type_var_with(typ.clone(), type_var.as_str(), type_param);
								return Ok(replaced_ty);
							}
						}
						Err(format!("struct {} does not have a {} field", struct_name, field))
					}
				},
				_ => Err(format!("{} is not a struct or pointer to a struct, cannot project off of it", base_typ))
			},
			Struct(ref struct_name) => match ctxt.structs.get(struct_name) {
				None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
				Some(NonGeneric(field_list)) => {
					/*
					if is_lhs is set and base is not a pointer and base itself is not an lvalue, error
					*/
					if ctxt.is_lhs && !matches!(base as &ast::Expr, Id(_) | Index(_,_) | Proj(_,_) | Deref(_)){
						return Err("Cannot assign to field of struct that is not an lvalue".to_owned());
					}
					for (field_name, typ) in field_list.iter() {
						if field.eq(field_name) {
							return Ok(typ.clone());
						}
					}
					Err(format!("struct {} does not have a {} field", struct_name, field))
				},
				Some(Generic{..}) => panic!("Proj: base type was {}, but struct context contained a generic struct", base_typ)
			},
			GenericStruct{type_var: ref type_param, name: ref struct_name} => match ctxt.structs.get(struct_name) {
				None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
				Some(NonGeneric(_)) => panic!("Proj: base had type {}, but struct context contained a non-generic struct for {}", base_typ, struct_name),
				Some(Generic{..}) =>  match ctxt.structs.get(struct_name) {
					None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
					Some(NonGeneric(_)) => panic!("Proj: base had type {}, but struct context contained a non-generic struct for {}", base_typ, struct_name),
					Some(Generic{mode: _, type_var, fields}) => {
						if ctxt.is_lhs && !matches!(base as &ast::Expr, Id(_) | Index(_,_) | Proj(_,_) | Deref(_)){
							return Err("Cannot assign to field of struct that is not an lvalue".to_owned());
						}
						for (field_name, typ) in fields.iter() {
							if field.eq(field_name) {
								let replaced_ty = replace_type_var_with(typ.clone(), type_var.as_str(), type_param);
								return Ok(replaced_ty);
							}
						}
						Err(format!("struct {} does not have a {} field", struct_name, field))
					}
				}
			},
			_ => Err(format!("{} is not a struct or pointer to a struct, cannot project off of it", base_typ))
		}
	},
	Call(func_name, args) => {
		use FuncType::*;
		if PRINTF_FAMILY.contains(&func_name.as_str()){
			typecheck_printf(func_name.as_str(), args as &[ast::Expr], ctxt, funcs)?;
			return Ok(Int{signed: true, size: ast::IntSize::Size32});
		}
		let return_type;
		let arg_type_list;
		match funcs.get(func_name) {
			None => {
				return Err(format!("could not find a function named '{}'", func_name));
			},
			Some(NonGeneric{return_type: None, ..}) => {
				return Err(format!("function '{}' returns void, cannot be used as an expression", func_name));
			},
			Some(Generic{..}) => {
				return Err(format!("function '{}' is generic", func_name))
			},
			Some(NonGeneric{return_type: Some(ret), args: arg_types}) => {
				return_type = ret.clone();
				arg_type_list = arg_types;
			}
		};
		if args.len() != arg_type_list.len() {
			return Err(format!("wrong number of args to {}: given {} args, should be {}", func_name, args.len(), arg_type_list.len()));
		}
		for (index, (given_type, correct_type)) in args.iter()
				.zip(arg_type_list.iter())
				.map(|(arg, expected_type)| {
					ctxt.type_for_lit_nulls = Some(expected_type.clone());
					(typecheck_expr(ctxt, funcs, arg), expected_type)
					})
				.enumerate(){
			//not doing array-to-pointer decay like c, do &arr[0] instead
			let given_type = given_type?;
			if given_type.ne(&correct_type) {
				return Err(format!("argument {} to {} has type {}, expected {}", index, func_name, given_type, correct_type));
			}
		}
		Ok(return_type)
	},
	GenericCall{name: func_name, type_var: type_param, args} => {
		use FuncType::*;
		all_struct_names_valid(&type_param, &ctxt.structs, &ctxt.type_var)?;
		let return_type;
		let arg_type_list;
		let callee_mode;
		let type_var_string;
		match funcs.get(func_name) {
			None => {
				return Err(format!("could not find a function named '{}'", func_name));
			},
			Some(Generic{return_type: None, ..}) => {
				return Err(format!("function '{}' returns void, cannot be used as an expression", func_name));
			},
			Some(NonGeneric{..}) => {
				return Err(format!("function '{}' is not generic", func_name))
			},
			Some(Generic{return_type: Some(ret), mode, type_var: var_string, args: arg_types}) => {
				return_type = ret.clone();
				arg_type_list = arg_types;
				callee_mode = mode;
				type_var_string = var_string;
			}
		};
		let type_var_str_in_type_var = type_param.recursively_find_type_var();
		match (type_var_str_in_type_var, &ctxt.type_var) {
			(None, _) => (),
			(Some(s), None) => return Err(format!("Cannot use type var '{} in non-generic function", s)),
			(Some(s), Some((current_func_type_var, current_func_mode))) => {
				if s != current_func_type_var {
					return Err(format!("type param passed to generic func {} contains unknown type var '{}", func_name, s));
				}
				use ast::PolymorphMode::*;
				if *callee_mode == Separated && *current_func_mode == Erased {
					return Err(format!("Cannot call separated function {} from erased function", func_name));
				}
			}
		};
		if args.len() != arg_type_list.len() {
			return Err(format!("wrong number of args to {}: given {} args, should be {}", func_name, args.len(), arg_type_list.len()));
		}
		/*
		expr is:		name@<type_param>(..args..)
		name has type:	return_type name@<var_string>(..arg_type_list..)
		the monomorphed version of name would look like:
						return_type name_mangled_type_var(..arg_type_list with var_string replaced with type_var..)
		*/
		for (index, (given_type, correct_type)) in args.iter() //Expr
				.zip(arg_type_list.iter()) //(Expr, Ty)
				.enumerate() //(usize, (Expr, Ty))
				.map(|(index, (arg, expected_type))| { //(usize, (Ty, Ty))
					let correct_type = replace_type_var_with(expected_type.clone(), type_var_string.as_str(), type_param);
					ctxt.type_for_lit_nulls = Some(correct_type.clone());
					(index, (typecheck_expr(ctxt, funcs, arg), correct_type))
				}){
			let given_type = given_type?;
			if given_type != correct_type {
				return Err(format!("argument {} to {} has type {}, expected {}", index, func_name, given_type, correct_type));
			}
		};
		/*
		current context type var is 'A
		expr is func_name@<type_param which contains 'A>(..args..)
		func_name is declared with type return_type func_name@<(erased|separated) 'C>(..arg_type_list..)
		this expr has type (return_type with 'C replaced with type_param)
		*/
		let replaced_type_var = replace_type_var_with(return_type, type_var_string, type_param);
		Ok(replaced_type_var)
	},
	Cast(dest_type, source) => {
		all_struct_names_valid(&dest_type, &ctxt.structs, &ctxt.type_var)?;
		let type_var_str_in_dest_type = dest_type.recursively_find_type_var();
		match (type_var_str_in_dest_type, &ctxt.type_var) {
			(Some(s), None) => return Err(format!("Cannot use type var '{} in non-generic function", s)),
			(Some(s), Some((current_func_type_var, _))) if s != current_func_type_var => {
				return Err(format!("Type used in cast contains unknown type var '{}", s));
			},
			_ => ()
		};
		ctxt.type_for_lit_nulls = Some(Ptr(None));
		let original_type = typecheck_expr(ctxt, funcs, source)?;
		match (original_type, dest_type) {
			(Int{..}, Int{..})
		  | (Ptr(_), Ptr(_))
		  | (Float(_), Float(_))
		  | (Float(_), Int{..}) | (Int{..}, Float(_))
		  | (Bool, Int{..}) => Ok(dest_type.clone()),
			
			(TypeVar(v), _) => Err(format!("Cannot cast from '{}", v)),
			(_, TypeVar(v)) => Err(format!("Cannot cast to '{}", v)),
			(original_type, dest_type) => Err(format!("Cannot cast from {} to {}", original_type, dest_type))
			
		}
	},
	Binop(left, bop, right) => {
		use ast::BinaryOp::*;
		ctxt.type_for_lit_nulls = Some(Ptr(None));
		let left_type = typecheck_expr(ctxt, funcs, left)?;
		ctxt.type_for_lit_nulls = Some(Ptr(None));
		let right_type = typecheck_expr(ctxt, funcs, right)?;
		match bop {
			Add | Sub => match (left_type, right_type) {
				//when doing pointer arithmetic, the pointer must be the left hand side, and the integer must be the right hand side
				//this avoids issues with subtraction of pointers
				(original @ Ptr(_), Int{..}) => Ok(original),
				(Int{..}, Ptr(_)) => Err("when doing pointer arithmetic, the pointer must be the left hand side, and the integer must be the right hand side".to_owned()),
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: sign1, size: if size1 > size2 {size1} else {size2}}),
				(Int{..}, Int{..}) => Err("Cannot add/sub integers with different signedness".to_owned()),
				(Float(size1), Float(size2)) => Ok(Float(if size1 > size2 {size1} else {size2})),
				(left_type, right_type) => Err(format!("Cannot add/sub types {} and {}", left_type, right_type))
			},
			Mul | Div | Mod => match (left_type, right_type) {
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: sign1, size: if size1 > size2 {size1} else {size2}}),
				(Int{..}, Int{..}) => Err("Cannot mul/div/mod integers with different signedness".to_owned()),
				(Float(size1), Float(size2)) => Ok(Float(if size1 > size2 {size1} else {size2})),
				(left_type, right_type) => Err(format!("Cannot mul/div/mod types {} and {}", left_type, right_type))
			},
			Lt | Lte | Gt | Gte | Equ | Neq => match (left_type, right_type) {
				(Int{signed: sign1,..}, Int{signed: sign2,..}) if sign1 != sign2 => Err("Cannot compare signed and unsigned int".to_owned()),
				(Int{..}, Int{..}) | (Float(_), Float(_)) => {
					Ok(Bool)
				},
				(left_type, right_type) if left_type == right_type => match left_type {
					Struct(name) | GenericStruct{name, ..} => Err(format!("Cannot compare struct {}", name)),
					Array{..} => Err("Cannot compare arrays".to_owned()),
					_ => Ok(Bool)
				},
				(left_type, right_type) => Err(format!("Cannot compare types {} and {}", left_type, right_type))
			},
			And | Or => match (left_type, right_type) {
				(Bool, Bool) => Ok(Bool),
				(left_type, right_type) => Err(format!("Cannot logical and/or types {} and {}", left_type, right_type))
			},
			Bitand | Bitor | Bitxor => match (left_type, right_type) {
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: sign1, size: if size1 > size2 {size1} else {size2}}),
				(left_type, right_type) => Err(format!("Cannot bitand/bitor/bitxor types {} and {}", left_type, right_type))
			},
			Shl | Shr | Sar => match (left_type, right_type) {
				(left_type @ Int{..}, Int{..}) => Ok(left_type),
				(left_type, right_type) => Err(format!("Cannot shl/shr/sar types {} and {}", left_type, right_type))
			}
		}
	},
	Unop(op, e) => {
		use ast::UnaryOp::*;
		ctxt.type_for_lit_nulls = Some(Ptr(None));
		match op {
		Neg => match typecheck_expr(ctxt, funcs, e)? {
			original @ Int{signed: true, ..} 
		  | original @ Float(_) => Ok(original),
			Int{signed: false, ..} => Err("Cannot negate an unsigned int".to_owned()),
			other => Err(format!("Cannot negate type {}", other))
		},
		Lognot => match typecheck_expr(ctxt, funcs, e)? {
			Bool => Ok(Bool),
			other => Err(format!("Cannot do logical not of type {}", other))
		},
		Bitnot => match typecheck_expr(ctxt, funcs, e)? {
			original @ Int{..} => Ok(original),
			other => Err(format!("Cannot bitwise negate type {}", other))
		}
	}},
	GetRef(e) => {
		let e_type = typecheck_expr(ctxt, funcs, e)?;
		//don't need to set type_for_lit_nulls here because it will already be an error anyway
		match **e {
			Id(_) | Proj(_,_) | Index(_,_) | Deref(_) => Ok(Ptr(Some(Box::new(e_type)))),
			_ => Err(format!("Cannot get address of {:?}", e))
		}
	},
	Deref(e) => {
		ctxt.type_for_lit_nulls = Some(Ptr(None));
		let e_type = typecheck_expr(ctxt, funcs, e)?;
		match e_type {
			Ptr(Some(t)) => Ok(*t),
			_ => Err(format!("Cannot dereference type {}", e_type))
		}
	},
	Sizeof(t) => {
		all_struct_names_valid(&t, &ctxt.structs, &ctxt.type_var)?;
		//Not sure how to handle sizeof a type var
		//current idea: size of a separated type var gets resolved after instatiation,
		//size of an erased type var is computed at runtime
		//in both cases, it is a u64
		let type_var_str_in_type = t.recursively_find_type_var();
		match (type_var_str_in_type, &ctxt.type_var) {
			(Some(s), None) => return Err(format!("Cannot use type var '{} in non-generic function", s)),
			(Some(s), Some((current_func_type_var, _))) if s != current_func_type_var => {
				return Err(format!("Type param used in sizeof contains unknown type var '{}", s));
			},
			_ => ()
		};
		Ok(Int{signed:false, size: Size64})
	}
}
}

pub fn typecheck_stmt(ctxt: &mut LocalTypeContext, funcs: &FuncContext, s: &ast::Stmt, expected_return_type: &Option<ast::Ty>) -> Result<bool, String> {
use ast::Ty::*;
use ast::Expr::*;
use ast::Stmt::*;
match s {
	Assign(lhs, rhs) => {
		match lhs {
			Id(_) | Index(_,_) | Proj(_,_) | Deref(_) => {
				ctxt.is_lhs = true;
				let lhs_type = typecheck_expr(ctxt, funcs, &lhs)?;
				ctxt.is_lhs = false;
				ctxt.type_for_lit_nulls = Some(lhs_type.clone());
				let rhs_type = typecheck_expr(ctxt, funcs, &rhs)?;
				if lhs_type != rhs_type {
					Err(format!("Cannot assign value of type {} to something of type {}", rhs_type, lhs_type))
				} else {
					Ok(false)
				}
			},
			_ => Err(format!("Left-hand-side of assignment cannot be a {:?}", lhs))
		}
	},
	Decl(typ, name) => {
		all_struct_names_valid(&typ, &ctxt.structs, &ctxt.type_var)?;
		let type_var_str_in_decl_type = typ.recursively_find_type_var();
		match (type_var_str_in_decl_type, &ctxt.type_var) {
			(Some(s), None) => return Err(format!("Cannot use type var '{} in non-generic function", s)),
			(Some(s), Some((current_func_type_var, _))) if s != current_func_type_var => {
				return Err(format!("Type used in declaration of {} contains unknown type var '{}", name, s));
			},
			_ => ()
		};
		if ctxt.locals.contains_key(name){
			Err(format!("redeclaration of local var {}", name))
		} else {
			ctxt.locals.insert(name.clone(), typ.clone());
			Ok(false)
		}
	},
	Return(None) => {
		if None.eq(expected_return_type) {
			Ok(true)
		} else {
			Err("Cannot return void in a non-void function".to_owned())
		}
	},
	Return(Some(e)) => {
		match expected_return_type {
			None => Err("Cannot return a value from a void function".to_owned()),
			Some(t) => {
				ctxt.type_for_lit_nulls = Some(t.clone());
				let return_expr_type = typecheck_expr(ctxt, funcs, &e)?;
				if return_expr_type.ne(t) {
					Err(format!("Cannot return a value of type {} in a function that returns {}", return_expr_type, t))
				} else {
					Ok(true)
				}
			}
		}
	},
	SCall(func_name, args) => {
		use FuncType::*;
		if PRINTF_FAMILY.contains(&func_name.as_str()){
			typecheck_printf(func_name.as_str(), args as &[ast::Expr], ctxt, funcs)?;
			return Ok(false);
		}
		let arg_type_list;
		match funcs.get(func_name) {
			None => {
				return Err(format!("could not find a function named '{}'", func_name));
			},
			Some(Generic{..}) => {
				return Err(format!("function '{}' is generic", func_name))
			},
			Some(NonGeneric{args: arg_types, ..}) => {
				arg_type_list = arg_types;
			}
		};
		if args.len() != arg_type_list.len() {
			return Err(format!("wrong number of args to {}: given {} args, should be {}", func_name, args.len(), arg_type_list.len()));
		}
		for (index, (given_type, correct_type)) in args.iter()
				.zip(arg_type_list.iter())
				.map(|(arg, expected_type)| {
					ctxt.type_for_lit_nulls = Some(expected_type.clone());
					(typecheck_expr(ctxt, funcs, arg), expected_type)
				})
				.enumerate(){
			let given_type = given_type?;
			if given_type.ne(&correct_type) {
				return Err(format!("argument {} to {} has type {}, expected {}", index, func_name, given_type, correct_type));
			}
		}
		Ok(false)
	},
	GenericSCall{name: func_name, type_var, args} => {
		use FuncType::*;
		all_struct_names_valid(&type_var, &ctxt.structs, &ctxt.type_var)?;
		let arg_type_list;
		let callee_mode;
		let type_var_string;
		match funcs.get(func_name) {
			None => {
				return Err(format!("could not find a function named '{}'", func_name));
			},
			Some(NonGeneric{..}) => {
				return Err(format!("function '{}' is not generic", func_name))
			},
			Some(Generic{mode, type_var: var_string, args: arg_types, ..}) => {
				arg_type_list = arg_types;
				callee_mode = mode;
				type_var_string = var_string;

			}
		};
		let type_var_str_in_type_var = type_var.recursively_find_type_var();
		match (type_var_str_in_type_var, &ctxt.type_var) {
			(None, _) => (),
			(Some(s), None) => return Err(format!("Cannot use type var '{} in non-generic function", s)),
			(Some(s), Some((current_func_type_var, current_func_mode))) => {
				if s != current_func_type_var {
					return Err(format!("type param passed to generic func {} contains unknown type var '{}", func_name, s));
				}
				use ast::PolymorphMode::*;
				if *callee_mode == Separated && *current_func_mode == Erased {
					return Err(format!("Cannot call separated function {} from erased function", func_name));
				}
			}
		};
		if args.len() != arg_type_list.len() {
			return Err(format!("wrong number of args to {}: given {} args, should be {}", func_name, args.len(), arg_type_list.len()));
		}
		/*
		expr is:		name<type_var>(..args..)
		name has type:	return_type name<var_string>(..arg_type_list..)
		the monomorphed version of name would look like:
						return_type name_mangled_type_var(..arg_type_list with var_string replaced with type_var..)
		*/
		for (index, (given_type, correct_type)) in args.iter() //Expr
				.zip(arg_type_list.iter()) //(Expr, Ty)
				.enumerate() //(usize, (Expr, Ty))
				.map(|(index, (arg, expected_type))| { //(usize, (Ty, Ty))
					let correct_type = replace_type_var_with(expected_type.clone(), type_var_string.as_str(), type_var);
					ctxt.type_for_lit_nulls = Some(correct_type.clone());
					(index, (typecheck_expr(ctxt, funcs, arg), correct_type))
				}){
			let given_type = given_type?;
			if given_type != correct_type {
				return Err(format!("argument {} to {} has type {}, expected {}", index, func_name, given_type, correct_type));
			}
		};
		Ok(false)
	},
	If(cond, then_block, else_block) => {
		ctxt.type_for_lit_nulls = Some(Bool);
		let cond_type = typecheck_expr(ctxt, funcs, &cond)?;
		if cond_type != Bool {
			return Err(format!("condition of if statement must have type bool, not {}", cond_type));
		}
		let then_returns = typecheck_block(ctxt, funcs, then_block, expected_return_type)?;
		let else_returns = typecheck_block(ctxt, funcs, else_block, expected_return_type)?;
		Ok(then_returns && else_returns)
	},
	While(cond, body) => {
		ctxt.type_for_lit_nulls = Some(Bool);
		let cond_type = typecheck_expr(ctxt, funcs, &cond)?;
		if cond_type != Bool {
			return Err(format!("condition of while statement must have type bool, not {}", cond_type));
		}
		let _ = typecheck_block(ctxt, funcs, body, expected_return_type)?;
		Ok(false)
	}
}
}

pub fn typecheck_block(ctxt: &mut LocalTypeContext, funcs: &FuncContext, block: &[ast::Stmt], expected_return_type: &Option<ast::Ty>) -> Result<bool, String> {
	let mut stmt_returns = false;
	for stmt in block.iter(){
		if stmt_returns {
			return Err("definite return on statement that is not the last in a block".to_owned())
		}
		stmt_returns = typecheck_stmt(ctxt, funcs, stmt, expected_return_type)?;
	}
	Ok(stmt_returns)
}

pub fn typecheck_func_decl(ctxt: &mut LocalTypeContext, funcs: &FuncContext, name: String, args: &[(ast::Ty, String)], body: &[ast::Stmt], ret_type: &Option<ast::Ty>) -> Result<(), String>{
	/*
	create a LocalTypeContext
	add all args to it as locals
	if ret_type is not None, make sure body definitely returns
	*/
	for (arg_ty, arg_name) in args.iter().cloned() {
		ctxt.locals.insert(arg_name, arg_ty);
	}
	//add errno to the LocalTypeContext as a local variable with type i32
	ctxt.locals.insert("errno".to_owned(), ast::Ty::Int{signed: true, size: ast::IntSize::Size32});
	let last_statement_definitely_returns = typecheck_block(ctxt, funcs, body, ret_type)?;
	if ret_type.is_some() && !last_statement_definitely_returns {
		return Err(format!("function '{}' might not return", name));
	}
	Ok(())
	
}

fn traverse_struct_context(struct_context: &StructContext) -> Result<(), String> {
	/*
	nodes are (struct_name, type_param)
	the edge (A, t1) -> (B, t2) exists iff there is a field in struct A@<t1> that has type
	struct B@<t3>, where t3 is t2 with A's type var replaced with B's
	TODO: if I see a node (A, concrete_type) in this traversal and A is a separated struct, then
	it is one of the struct instatiations I will need to create later. This function could return
	this information for later use.
	*/
	use std::collections::VecDeque;
	use StructType::*;
	//Possible Improvement: make type Node = (&str, Option<&Ty>)
	//use pool allocator to wrap type_var in TypeVar
	//this eliminates cloning of tys
	type Node<'a> = (&'a str, Option<ast::Ty>);
	const MAX_STRUCT_DEPTH: i32 = 100;
	let mut fully_explored_nodes: HashSet<Node> = HashSet::with_capacity(struct_context.len());
	let mut queue: VecDeque<Node> = VecDeque::with_capacity(struct_context.len());
	for (name, struct_type) in struct_context.iter(){
		let node = match struct_type {
			NonGeneric(_) => (name.as_str(), None),
			Generic{type_var, ..} => {
				let new_ty = ast::Ty::TypeVar(type_var.clone());
				(name.as_str(), Some(new_ty))
			}
		};
		if fully_explored_nodes.contains(&node) { continue }
		queue.push_back(node);
		let mut seen_nodes: HashSet<Node> = HashSet::with_capacity(struct_context.len());
		let mut iterations = 0;
		while !queue.is_empty() {
			iterations += 1;
			if iterations >= MAX_STRUCT_DEPTH {
				return Err(format!("maximum struct depth ({}) reached when processing struct '{}'", MAX_STRUCT_DEPTH, name));
			}
			let current_node = queue.pop_front().unwrap();
			if fully_explored_nodes.contains(&current_node) {
				continue
			}
			if seen_nodes.contains(&current_node) {
				return Err(format!("struct '{}' is recursive", current_node.0));
			}
			seen_nodes.insert(current_node.clone());
			let struct_type = struct_context.get(current_node.0).expect("why is this not in the struct context?");
			let fields = match struct_type {
				NonGeneric(fields) => fields,
				Generic{fields, ..} => fields
			};
			//investigating the fields in a generic struct is fundamentally different than in a non-generic struct,
			//so they are handled dirrerently here
			match current_node.1 {
			//current node is a non-generic struct
			None => {
				for field_type in fields.iter().map(|(_, t)| t){
					if field_type.recursively_find_type_var().is_some() {
						return Err(format!("non-generic struct {} has a field of type {}", current_node.0, field_type));
					}
					use ast::Ty::*;
					match field_type {
						Struct(s) => queue.push_back((s.as_str(), None)),
						GenericStruct{type_var: fully_concrete_type, name} => queue.push_back((name.as_str(), Some((&fully_concrete_type as &ast::Ty).clone()))),
						_ => ()
					}
				}
			},
			//current node is a generic struct
			Some(type_param) => {
				//If the type_param is a concrete type, then I need to treat any instances of
				//the current struct's type param string as this type
				//to get the type param string, need to look up current_node.0 in struct_context

				let (current_mode, type_param_string_of_current_struct): (ast::PolymorphMode, &str) = match struct_context.get(current_node.0).expect("why is the current struct's name not in the context?") {
					NonGeneric{..} => panic!("why is struct {} generic and non-generic?", current_node.0),
					Generic{type_var, mode, ..} => (*mode, type_var.as_str())
				};
				//the current type param can be concrete even if it is just a TypeVar.
				//It could be a different TypeVar
				let type_param_is_concrete: bool = type_param != ast::Ty::TypeVar(type_param_string_of_current_struct.to_owned());
				for field_type in fields.iter().map(|(_, t)| t){
					use ast::Ty::*;
					match (type_param_is_concrete, field_type.recursively_find_type_var()) {
						//make sure a struct with a TypeVar type param does not have any fields with other TypeVars
						(false, Some(field_param_str)) => {
							if type_param_string_of_current_struct != field_param_str {
								return Err(format!("struct {}@<'{}> has a field with an unknown type param, {}", current_node.0, type_param_string_of_current_struct, field_type));
							}
						},
						//make sure a struct a concrete type param does not have any fields with a TypeVar that is not the current struct's type var
						(true, Some(typevar)) if typevar != type_param_string_of_current_struct => {
							return Err(format!("struct {}@<{}> has a field with an unknown type param, {}", current_node.0, type_param, field_type));
						}
						_ => ()
					};
					//any TypeVars encountered henceforth are guaranteed to be valid,
					//but I will debug_assert them anyway
					match field_type {
						Struct(s) => queue.push_back((s.as_str(), None)),
						GenericStruct{type_var, name} => {
							//if the current struct is erased, and the field struct is separated, and
							//the current struct is passing its TypeVar to it (type param is not concrete),
							//then there is an error
							let field_mode = match struct_context.get(name).expect("field does not exist") {
								NonGeneric{..} => panic!("why is struct {} generic and non-generic?", name),
								Generic{mode, ..} => mode
							};
							use ast::PolymorphMode::*;
							let type_param_found_in_type_var = type_var.recursively_find_type_var();
							let field_type_param_is_concrete = type_param_found_in_type_var.is_none();
							if current_mode == Erased
								&& *field_mode == Separated
								&& !field_type_param_is_concrete {
								return Err(format!("struct {} passes an erased type var ('{}) to separated struct {}", current_node.0, type_param_string_of_current_struct, name));
							}
							let substituted1 = replace_type_var_with((type_var as &ast::Ty).clone(), type_param_string_of_current_struct, &type_param);
							let type_param_string_of_field_struct: &str = match struct_context.get(name).unwrap_or_else(|| panic!("why is struct {} not in the context?", name)) {
								NonGeneric{..} => panic!("why is field struct {} generic and non-generic?", name),
								Generic{type_var, ..} => type_var.as_str()
							};
							let substituted2 = replace_type_var_with(substituted1, type_param_string_of_current_struct, &TypeVar(type_param_string_of_field_struct.to_owned()));
							queue.push_back((name.as_str(), Some(substituted2)));

							/*
							match (type_param_is_concrete, &type_var as &ast::Ty) {
								//struct A@<'a> has a field of type struct B@<some type that contains 'a>
								//If the current node represents struct A@<'a>, and a field of type
								//struct B@<something with 'a> is seen, then there should really be an outgoing
								//edge to B@<'b>, instead of B@<'a>
								(false, TypeVar(field_type_var_string)) => {
									debug_assert!(type_param_string_of_current_struct == field_type_var_string, format!("struct {}@<'{}> has a generic struct field with an unknown type param (struct {}@<'{}>), this should have been detected already", current_node.0, type_param_string_of_current_struct, name, field_type_var_string));
									let type_param_of_field_struct: &str = match struct_context.get(name) {
										Some(Generic{type_var, ..}) => type_var.as_str(),
										Some(_) => panic!("How is struct {} generic and non-generic?", name),
										None => panic!("struct {} does not exist. non-existant structs should have been detected before calling traverse_struct_context.", name)
									};
									queue.push_back((name.as_str(), Some(TypeVar(type_param_of_field_struct.to_owned()))));
								},

								//struct A@<'a> has a field of type struct B@<'b>
								//already handled in above match arm

								//struct A@<concrete_base_type> has a field of type struct B@<'b>
								(true, TypeVar(field_type_var_string)) if field_type_var_string != type_param_string_of_current_struct => {
									panic!("a generic struct with a concrete base type (struct {}@<{}>) was found to have a field that is a generic struct with an unresolved TypeVar ('{}).", current_node.0, type_param, field_type_var_string);
								},

								//struct A@<concrete_base_type> has a field of type struct B@<some type that includes 'a>
								//there should really be an outgoing edge to B@<that type with 'a replaced with the current type param>
								(true, field_type_var) => {
									let replaced = replace_type_var_with(field_type_var.clone(), found_typevar, type_param.clone());
									queue.push_back((name.as_str(), Some(replaced)));
								}

								//field has type struct B@<concrete_type>
								(_, concrete_type) => {
									//above arm should catch all cases where type_param_is_concrete is true
									debug_assert!(!type_param_is_concrete, "got to the last case when the type param is concrete, how did this happen?");
									queue.push_back(
										(name.as_str(), Some(concrete_type.clone()))
									);
								},

							}
							*/
						},
						//If struct A@<concrete type> has a field that is 'a, 'a* or 'a[], I don't
						//bother replacing it with the concrete type because I don't think this could
						//cause any recursiveness/infinite sized structs
						_ => ()
					}
				}
			}
			}
		}
		//seen_nodes is now full of nodes that are completely explored and known not to have
		//any cycles, so they can be transferred to fully_explored_nodes
		fully_explored_nodes.extend(seen_nodes.into_iter());
	};
	Ok(())
}

//makes sure that a type declared in an extern function is compatible with the C type system
//No TypeVars or GenericStructs, either directly contained within struct fields
fn type_is_c_compatible(t: &ast::Ty, structs: &StructContext) -> bool { use ast::Ty::*; match t {
	Ptr(Some(boxed)) => type_is_c_compatible(boxed as &ast::Ty, structs),
	Array{typ, ..} => type_is_c_compatible(typ as &ast::Ty, structs),
	Struct(s) => { match structs.get(s).unwrap() {
		StructType::Generic{..} => panic!("struct {} is a generic struct in the context, should have been caught by now by calling all_struct_names_valid", s),
		StructType::NonGeneric(fields) => fields.iter().all(|(_, field_ty)| type_is_c_compatible(field_ty, structs))
	}},
	TypeVar(_) | GenericStruct{..} => false,
	_ => true
}}

pub struct ProgramContext {
	pub structs: StructContext,
	pub funcs: FuncContext,
	pub globals: GlobalContext
}

pub fn typecheck_program(gdecls: &[ast::Gdecl]) -> Result<ProgramContext, String>{
	/*
	create StructContext:
		collect names of all structs, put all of them into struct_context
			make sure a struct with this name does not already exist
		for each struct in struct_context:
			make sure there are no duplicate field
			make sure each field has a valid type
	create FuncContext:
	create GlobalContext:
		for each GFuncDecl (or GGenericFuncDecl, later):
			make sure a function or global var with this name does not already exist
			make sure the type signature of the function contains valid types
			make sure the there are no duplicates in the names of the arguments
			put it in the FuncContext
		for each GVarDecl:
			make sure there are no functions or other vars with this name
			put them all in a GlobalContext
	typecheck all functions with typecheck_func_decl (or typecheck_generic_func_decl, later)
	*/
	let mut struct_context: StructContext = HashMap::new();
	for g in gdecls.iter() { match g {
		GStructDecl{name, fields} => {
			if struct_context.contains_key(name){
				return Err(format!("struct '{}' is declared more than once", name));
			}
			struct_context.insert(name.clone(), StructType::NonGeneric(fields.iter().cloned().map(|(t, n)| {(n, t)}).collect()));
		},
		GGenericStructDecl{name, param, mode, fields} => {
			if struct_context.contains_key(name){
				return Err(format!("struct '{}' is declared more than once", name));
			}
			struct_context.insert(name.clone(), StructType::Generic{
				mode: *mode,
				type_var: param.clone(),
				fields: fields.iter().cloned().map(|(t, n)| (n, t)).collect()
			});
		},
		_ => ()
	}}
	//struct_context has been populated, now need to check for duplicate and invalid fields
	for (name, struct_type) in struct_context.iter(){
		use StructType::*;
		match struct_type {
		NonGeneric(fields) => {
			let mut seen_fields: HashSet<&str> = HashSet::new();
			for (field_name, field_type) in fields.iter(){
				if seen_fields.contains(field_name.as_str()){
					return Err(format!("struct {} contains two fields named {}", name, field_name));
				}
				all_struct_names_valid(field_type, &struct_context, &None)?;
				seen_fields.insert(field_name.as_str());
			}
		},
		Generic{type_var, fields, mode} => {
			let mut seen_fields: HashSet<&str> = HashSet::new();
			for (field_name, field_type) in fields.iter(){
				if seen_fields.contains(field_name.as_str()){
					return Err(format!("struct {} contains two fields named {}", name, field_name));
				}
				all_struct_names_valid(field_type, &struct_context, &Some((type_var.clone(), *mode)))?;
				seen_fields.insert(field_name.as_str());
			}
		}
	}}
	traverse_struct_context(&struct_context)?;

	let mut func_context: FuncContext = HashMap::new();
	let mut global_context: GlobalContext = HashMap::new();
	use ast::Gdecl::*;

	//first, check all external decls for c compatibility, and add them to the func_context
	for g in gdecls.iter() { if let Extern{ret_type, name, arg_types} = g {
		if global_context.contains_key(name) {
			return Err(format!("Cannot declare an extern function named \"{}\", there is already a global variable with that name", name));
		}
		for (i, arg_type) in arg_types.iter().enumerate() {
			all_struct_names_valid(arg_type, &struct_context, &None)?;
			if !type_is_c_compatible(arg_type, &struct_context) {
				return Err(format!("argument {} to extern function {} has type {:?}, which is not C-compatible", i+1, name, arg_type));
			}
		}
		if let Some(ret) = ret_type {
			all_struct_names_valid(ret, &struct_context, &None)?;
			if !type_is_c_compatible(ret, &struct_context) {
				return Err(format!("extern function {} has return type {:?}, which is not C-compatible", name, ret));
			}
		}
		func_context.insert(name.clone(), FuncType::NonGeneric{
			return_type: ret_type.clone(),
			args: arg_types.clone()
		});
	}}
	for g in gdecls.iter() { match g {
		GFuncDecl{ret_type, name: func_name, args, ..} => {
			if func_context.contains_key(func_name) {
				return Err(format!("function '{}' is declared more than once", func_name));
			}
			if global_context.contains_key(func_name) {
				return Err(format!("cannot declare a function named '{}', a global variable of that name already exists", func_name));
			}
			if let Some(ret) = ret_type{
				all_struct_names_valid(&ret, &struct_context, &None)?;
				if let Some(s) = ret.recursively_find_type_var() {
					return Err(format!("found type variable '{} in return type of non-generic function {}", s, func_name));
				}
			}
			let mut names: HashSet<String> = HashSet::new();
			for (arg_type, arg_name) in args.iter().by_ref(){
				if names.contains(arg_name){
					return Err(format!("function '{}' contains two arguments both named '{}'", func_name, arg_name));
				}
				names.insert(arg_name.clone());
				all_struct_names_valid(&arg_type, &struct_context, &None)?;
				if let Some(s) = arg_type.recursively_find_type_var() {
					return Err(format!("found type variable '{} in type signature of non-generic function {}", s, func_name));
				}
			}
			func_context.insert(func_name.clone(), FuncType::NonGeneric{
				return_type: ret_type.clone(),
				args: args.iter().cloned().map(|(t, _)| t).collect()
			});
		},
		GGenericFuncDecl{name: func_name, ret_type, args, param, mode, ..} => {
			if func_context.contains_key(func_name) {
				return Err(format!("function '{}' is declared more than once", func_name));
			}
			if global_context.contains_key(func_name) {
				return Err(format!("cannot declare a function named '{}', a global variable of that name already exists", func_name));
			}
			if let Some(ret) = ret_type {
				all_struct_names_valid(&ret, &struct_context, &Some((param.clone(), *mode)))?;
				match ret.recursively_find_type_var() {
					Some(s) if s != param => return Err(format!("found unknown type variable '{} in return type of function {}", s, func_name)),
					_ => ()
				};
			}
			let mut names: HashSet<String> = HashSet::new();
			for (arg_type, arg_name) in args.iter().by_ref(){
				if names.contains(arg_name){
					return Err(format!("function '{}' contains two arguments both named '{}'", func_name, arg_name));
				}
				names.insert(arg_name.clone());
				all_struct_names_valid(&arg_type, &struct_context, &Some((param.clone(), *mode)))?;
				match arg_type.recursively_find_type_var() {
					Some(s) if s != param => return Err(format!("found unknown type variable '{} in type signature of function {}", s, func_name)),
					_ => ()
				}
			}
			func_context.insert(func_name.clone(), FuncType::Generic {
				return_type: ret_type.clone(),
				args: args.iter().cloned().map(|(t, _)| t).collect(),
				mode: *mode,
				type_var: param.clone(),
			});
		},
		//need to make sure there are no name collisions between global vars and functions
		GVarDecl(t, name) => {
			all_struct_names_valid(&t, &struct_context, &None)?;
			if let Some(s) = t.recursively_find_type_var() {
				return Err(format!("found type variable '{} in type of global variable", s));
			}
			if global_context.contains_key(name) {
				return Err(format!("cannot have two global variables both named '{}'", name));
			}
			if func_context.contains_key(name) {
				return Err(format!("cannot declare global variable '{}', a function is already declared with that name", name));
			}
			//a global var needs to have a known size at compile time, so it cannot be an erased struct,
			//or any array of erased structs, or a struct that contains an erased struct
			if t.is_DST(&struct_context, None) {
				return Err(format!("global variable {} does not have a statically known size because it contains an erased struct", name));
			}
			global_context.insert(name.clone(), t.clone());
		},
		GStructDecl{..} | GGenericStructDecl{..} | Extern{..} => ()
	}};
	for g in gdecls.iter().by_ref(){ match g {
		GFuncDecl{ret_type, name, args, body} => {
			let (mut ctxt, _) = get_empty_localtypecontext();
			//kind of weird, but in order to keep the LocalTypeContext the same and avoid
			//cloning the struct_context all the time, I need to move it into this temporary
			//ctxt variable, then move it back out (same for global_context)
			ctxt.globals = global_context;
			ctxt.structs = struct_context;
			typecheck_func_decl(&mut ctxt, &func_context, name.clone(), args, body, ret_type)?;
			struct_context = ctxt.structs;
			global_context = ctxt.globals;
		},
		GGenericFuncDecl{ret_type, name, args, body, param, mode} => {
			let (mut ctxt, _) = get_empty_localtypecontext();
			ctxt.type_var = Some((param.clone(), *mode));		
			ctxt.globals = global_context;
			ctxt.structs = struct_context;
			typecheck_func_decl(&mut ctxt, &func_context, name.clone(), args, body, ret_type)?;
			struct_context = ctxt.structs;
			global_context = ctxt.globals;
		}
		_ => ()
	}};

	//make sure main has the right type signature
	match func_context.get("main") {
		Some(FuncType::Generic{..}) => return Err("main() cannot be a generic function".to_owned()),
		Some(FuncType::NonGeneric{return_type, args}) => {
			let return_type_is_correct = return_type == &Some(ast::Ty::Int{
				signed: true, size: ast::IntSize::Size32
			});
			let args_are_correct_simple = args.is_empty();
			let args_are_correct_extended =
				args.len() == 2
				&& args[0] == ast::Ty::Int{
					signed: true, size: ast::IntSize::Size32
				}
				&& args[1] == ast::Ty::Ptr(Some(Box::new(ast::Ty::Ptr(Some(Box::new(
					ast::Ty::Int{
						signed: false, size: ast::IntSize::Size8
					}
				))))))
			;
			let args_are_correct = args_are_correct_simple || args_are_correct_extended;
			if !return_type_is_correct || !args_are_correct {
				return Err("main() must have type i32 main() or i32 main(i32, u8**)".to_owned());
			}
		},
		None => ()
	}
	Ok(ProgramContext{
		structs: struct_context,
		funcs: func_context,
		globals: global_context
	})
}
