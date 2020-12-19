use crate::ast;
use std::collections::{HashMap, HashSet};

/*
pub struct FuncType{
	pub args: Vec<ast::Ty>,
	pub return_type: Option<ast::Ty>
}
*/
pub enum FuncType{
	NonGeneric{return_type: Option<ast::Ty>, args: Vec<ast::Ty>},
	Generic{return_type: Option<ast::Ty>, mode: ast::PolymorphMode, type_var: String, args: Vec<ast::Ty>}
}

type LocalContext = HashMap<String, ast::Ty>;
type GlobalContext = HashMap<String, ast::Ty>;
type StructContext = HashMap<String, Vec<(String, ast::Ty)>>;
//TODO: complete type checker for regular structs, then see how StructContext is used,
//use this to figure out what GenericStructContext and GenericFuncContext should be
//type GenericStructContext = 

//FuncContext contains generic and non-generic functions
//a generic and non-generic function cannot share the same name
pub type FuncContext = HashMap<String, FuncType>;

pub struct LocalTypeContext{
	pub locals: LocalContext,
	pub globals: GlobalContext,
	pub structs: StructContext,
	pub type_var: Option<(String, ast::PolymorphMode)>,
	//TODO: one typechecking is done, find out when to set this
	pub type_for_lit_nulls: Option<ast::Ty>,
	//TODO: add a optional mode field here, and figure out what the rules for it should be
	//when typechecking a non-generic function, it will be None
	//when typechecking a generic function, this will be set to the mode that the function is using

}

pub fn get_empty_localtypecontext() -> (LocalTypeContext, FuncContext) {
	(LocalTypeContext{
		locals: HashMap::new(),
		globals: HashMap::new(),
		structs: HashMap::new(),
		type_var: None,
		type_for_lit_nulls: None
	},
	HashMap::new())
}

fn decay_type(t: ast::Ty) -> ast::Ty {
	match t {
		ast::Ty::Array{typ, ..} => ast::Ty::Ptr(Some(typ)),
		t => t
	}
}

fn all_struct_names_valid_set(t: &ast::Ty, structs: &HashSet<String>, generic_structs: &HashSet<String>) -> Result<(), String> {
	use ast::Ty::*;
	match t {
	Struct(s) => if structs.contains(s) { Ok(()) } else
		{ Err(format!("struct {} does not exist, or is generic", s)) },
	GenericStruct{name, ..} => if generic_structs.contains(name) { Ok(()) } else
		{ Err(format!("struct {} does not exist, or is not generic", name)) },
	Ptr(Some(t)) | Array{typ: t, ..} => all_struct_names_valid_set(t, structs, generic_structs),
	_ => Ok(())
}}

fn all_struct_names_valid_map<T, G>(t: &ast::Ty, structs: &HashMap<String, T>, generic_structs: &HashMap<String, G>) -> Result<(), String> {
	use ast::Ty::*;
	match t {
	Struct(s) => if structs.contains_key(s) {Ok(())} else
		{Err(format!("struct {} does not exist, or is generic", s))},
	GenericStruct{name, ..} => if generic_structs.contains_key(name) {Ok(())} else
		{Err(format!("struct {} does not exist, or is not generic", name))},
	Ptr(Some(t)) | Array{typ: t, ..} => all_struct_names_valid_map(t, structs, generic_structs),
	_ => Ok(())
}}

fn get_builtins() -> FuncContext {
	//printf functions do not go here, they are handled specially
	use ast::Ty::*;
	let mut result = HashMap::new();
	result.insert("malloc".to_owned(), FuncType::NonGeneric{
		return_type: Some(Ptr(None)),
		args: vec![
			Int{signed: false, size: ast::IntSize::Size64}
		]
	});
	result.insert("free".to_owned(), FuncType::NonGeneric{
		return_type: None,
		args: vec![
			Ptr(None)
		]
	});
	return result;

}

//when typechecking a function call, it the function is one of these, the
//number and type of arguments are not checked (each individual argument must
//still be well-typed though).
static PRINTF_FAMILY: &[&str] = &[
	"printf",
	"sprintf",
	"fprintf",
	"snprintf",
	"dprintf"
];

pub fn typecheck_expr(ctxt: &mut LocalTypeContext, funcs: &FuncContext, e: &ast::Expr) -> Result<ast::Ty, String>{
use ast::Ty::*;
use ast::Expr::*;
use ast::IntSize::*;
match e {
	LitNull => match &mut ctxt.type_for_lit_nulls {
		Some(t) => Ok(t.clone()),
		None => panic!("no type for this null")
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
	LitArr(init) => {
		if init.len() == 0 {
			eprintln!("Warning: Array literal has length 0, defaulting its type to i64[0]");
			return Ok(Array{length: 0, typ: Box::new(Int{signed:true, size:Size64})})
		}
		let first_type = typecheck_expr(ctxt, funcs, &init[0])?;
		for (index, init_expr) in init[1..].iter().enumerate() {
			let typ = typecheck_expr(ctxt, funcs, init_expr)?;
			if first_type.ne(&typ) {
				return Err(format!("Array literal has mismatching types, element 0 has type {:?}, element {} has type {:?}", first_type, index, typ));
			}
		}
		return Ok(Array{length: init.len() as u64, typ: Box::new(first_type)});
	},
	Index(base, index) => {
		let base_typ = typecheck_expr(ctxt, funcs, base)?;
		let result_type = match base_typ {
			Ptr(Some(typ)) | Array{typ, ..} => Ok(*typ),
			Ptr(None) => Err(format!("Can't index off of a void*")),
			_ => Err(format!("{:?} is not an array or pointer", base_typ))
		};
		if result_type.is_err() {
			return result_type;
		}
		let index_typ = typecheck_expr(ctxt, funcs, index)?;
		match index_typ {
			Int{..} => Ok(result_type.unwrap()),
			_ => Err(format!("Array indices must be integers, not {:?}", index_typ))
		}
	},
	Proj(base, field) => {
		let base_typ = typecheck_expr(ctxt, funcs, base)?;
		match base_typ {
			Struct(struct_name) => match ctxt.structs.get(&struct_name) {
				None => Err(format!("could not find struct named '{}'", struct_name)),
				Some(field_list) => {
					for (field_name, typ) in field_list.iter() {
						if field.eq(field_name) {
							return Ok(typ.clone());
						}
					}
					return Err(format!("struct {} does not have a {} field", struct_name, field));
				}
			},
			GenericStruct{type_var: _type_var, name: _name} => panic!("todo: projecting off a generic struct is not implemented in typechecker"),
			_ => Err(format!("{:?} is not a struct, project off of it", base_typ))
		}
	},
	Call(func_name, args) => {
		use FuncType::*;
		if PRINTF_FAMILY.contains(&func_name.as_str()){
			for arg in args.iter(){
				let _ = typecheck_expr(ctxt, funcs, arg)?;
			}
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
				.map(|arg| typecheck_expr(ctxt, funcs, arg))
				.zip(arg_type_list.iter())
				.enumerate(){
			let given_type = given_type?;
			let given_type_str = format!("{:?}", given_type);
			let given_type = decay_type(given_type);
			if given_type.ne(&correct_type) {
				return Err(format!("argument {} to {} has type {}, expected {:?}", index, func_name, given_type_str, correct_type));
			}
		}
		return Ok(return_type);
	},
	GenericCall{name: func_name, type_var, args} => {
		use FuncType::*;
		let return_type;
		let arg_type_list;
		//TODO: once the rules for interop between erased/separated structs/functions are established,
		//use this and the mod field in LocalTypeContext to check these rules
		let poly_mode;
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
				poly_mode = mode;
				type_var_string = var_string;

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
		for (index, (given_type, correct_type)) in args.iter()
				.map(|arg| typecheck_expr(ctxt, funcs, arg))
				.zip(arg_type_list.iter())
				.enumerate(){
			let given_type = given_type?;
			let given_type_str = format!("{:?}", given_type);
			let given_type = decay_type(given_type);
			let correct_type: &ast::Ty = match correct_type {
				TypeVar(s) => if s == type_var_string {&type_var} else {
					panic!("argument {} to function {} has type '{}, which is not the type var the function was declared with.\
					This should have been detected when typechecking the function's declaration.")
				},
				t => &t
			};
			if given_type.ne(correct_type) {
				return Err(format!("argument {} to {} has type {}, expected {:?}", index, func_name, given_type_str, correct_type));
			}
		};
		Ok(return_type)
	},
	Cast(dest_type, source) => {
		let original_type = typecheck_expr(ctxt, funcs, source)?;
		let original_type_string = format!("{:?}", original_type);
		let original_type = decay_type(original_type);
		match (original_type, dest_type) {
			(Int{..}, Int{..})
		  | (Ptr(_), Ptr(_))
		  | (Float(_), Float(_))
		  | (Bool, Int{..}) => Ok(dest_type.clone()),
			
			(TypeVar(_), _) | (_, TypeVar(_)) => panic!("trying to cast with a TypeVar, I don't know what to do here yet"),
			(_, _) => Err(format!("Cannot cast from {} to {:?}", original_type_string, dest_type))
			
		}
	},
	Binop(left, bop, right) => {
		use ast::BinaryOp::*;
		let left_type = typecheck_expr(ctxt, funcs, left)?;
		let right_type = typecheck_expr(ctxt, funcs, right)?;
		match bop {
			Add | Sub => match (left_type, right_type) {
				(original @ Ptr(_), Int{..}) => Ok(original),
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: sign1, size: if size1 > size2 {size1} else {size2}}),
				(Int{..}, Int{..}) => Err("Cannot add/sub integers with different signedness".to_owned()),
				(Float(size1), Float(size2)) => Ok(Float(if size1 > size2 {size1} else {size2})),
				(TypeVar(_), _) | (_, TypeVar(_)) => panic!("not sure how to handle a typevar here"),
				(left_type, right_type) => Err(format!("Cannot add/sub types {:?} and {:?}", left_type, right_type))
			},
			Mul | Div | Mod => match (left_type, right_type) {
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: sign1, size: if size1 > size2 {size1} else {size2}}),
				(Int{..}, Int{..}) => Err("Cannot mul/div/mod integers with different signedness".to_owned()),
				(Float(size1), Float(size2)) => Ok(Float(if size1 > size2 {size1} else {size2})),
				(left_type, right_type) => Err(format!("Cannot mul/div/mod types {:?} and {:?}", left_type, right_type))
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
				(left_type, right_type) => Err(format!("Cannot compare types {:?} and {:?}", left_type, right_type))
			},
			And | Or => match (left_type, right_type) {
				(Bool, Bool) => Ok(Bool),
				(left_type, right_type) => Err(format!("Cannot logical and/or types {:?} and {:?}", left_type, right_type))
			},
			Bitand | Bitor | Bitxor => match (left_type, right_type) {
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: sign1, size: if size1 > size2 {size1} else {size2}}),
				(left_type, right_type) => Err(format!("Cannot bitand/bitor/bitxor types {:?} and {:?}", left_type, right_type))
			},
			Shl | Shr | Sar => match (left_type, right_type) {
				(left_type @ Int{..}, Int{..}) => Ok(left_type),
				(left_type, right_type) => Err(format!("Cannot shl/shr/sar types {:?} and {:?}", left_type, right_type))
			}
		}
	},
	Unop(op, e) => {use ast::UnaryOp::*; match op {
		Neg => match typecheck_expr(ctxt, funcs, e)? {
			original @ Int{signed: true, ..} 
		  | original @ Float(_) => Ok(original),
			Int{signed: false, ..} => Err("Cannot negate an unsigned int".to_owned()),
			TypeVar(_) => panic!("not sure how to handle a typevar here"),
			other => Err(format!("Cannot negate type {:?}", other))
		},
		Lognot => match typecheck_expr(ctxt, funcs, e)? {
			Bool => Ok(Bool),
			TypeVar(_) => panic!("not sure how to handle a typevar here"),
			other => Err(format!("Cannot do logical not of type {:?}", other))
		},
		Bitnot => match typecheck_expr(ctxt, funcs, e)? {
			original @ Int{..} => Ok(original),
			TypeVar(_) => panic!("not sure how to handle a typevar here"),
			other => Err(format!("Cannot bitwise negate type {:?}", other))
		}
	}},
	GetRef(e) => {
		let e_type = typecheck_expr(ctxt, funcs, e)?;
		match **e {
			Id(_) | Proj(_,_) | Index(_,_) | Deref(_) => Ok(Ptr(Some(Box::new(e_type)))),
			_ => Err(format!("Cannot get address of {:?}", e))
		}
	},
	Deref(e) => {
		let e_type = typecheck_expr(ctxt, funcs, e)?;
		match e_type {
			Ptr(Some(t)) | Array{typ: t, ..} => Ok(*t.clone()),
			_ => Err(format!("Cannot dereference type {:?}", e_type))
		}
	},
	Sizeof(_) => Ok(Int{signed:false, size: Size64})
}
}

pub fn typecheck_stmt(ctxt: &mut LocalTypeContext, funcs: &FuncContext, s: &ast::Stmt, expected_return_type: &Option<ast::Ty>) -> Result<bool, String> {
use ast::Ty::*;
use ast::Expr::*;
use ast::Stmt::*;
match s {
	Assign(lhs, rhs) => {
		let rhs_type = typecheck_expr(ctxt, funcs, &rhs)?;
		match lhs {
			Id(_) | Index(_,_) | Proj(_,_) | Deref(_) => {
				let lhs_type = typecheck_expr(ctxt, funcs, &lhs)?;
				if lhs_type != rhs_type {
					Err(format!("Cannot assign value of type {:?} to something of type {:?}", rhs_type, lhs_type))
				} else {
					Ok(false)
				}
			},
			_ => Err(format!("Left-hand-side of assignment cannot be a {:?}", lhs))
		}
	},
	Decl(typ, name) => {
		//TODO: whenever the ast contains a Ty, check if it is a Struct or GenericStruct,
		//if it is, make sure it is in ctxt.structs (and probably ctxt.generic_structs, which doesn't exist yet)
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
		let return_expr_type = typecheck_expr(ctxt, funcs, &e)?;
		match expected_return_type {
			None => Err("Cannot return a value from a void function".to_owned()),
			Some(t) if return_expr_type.ne(t) => Err(format!("Cannot return a value of type {:?} in a function that returns {:?}", return_expr_type, t)),
			Some(_) => Ok(true)
		}
	},
	SCall(func_name, args) => {
		use FuncType::*;
		if PRINTF_FAMILY.contains(&func_name.as_str()){
			for arg in args.iter(){
				let _ = typecheck_expr(ctxt, funcs, arg)?;
			}
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
				.map(|arg| typecheck_expr(ctxt, funcs, arg))
				.zip(arg_type_list.iter())
				.enumerate(){
			let given_type = given_type?;
			let given_type_str = format!("{:?}", given_type);
			let given_type = decay_type(given_type);
			if given_type.ne(&correct_type) {
				return Err(format!("argument {} to {} has type {}, expected {:?}", index, func_name, given_type_str, correct_type));
			}
		}
		return Ok(false);
	},
	GenericSCall{name: func_name, type_var, args} => {
		use FuncType::*;
		let arg_type_list;
		//TODO: once the rules for interop between erased/separated structs/functions are established,
		//use this and the mod field in LocalTypeContext to check these rules
		let poly_mode;
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
				poly_mode = mode;
				type_var_string = var_string;

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
		for (index, (given_type, correct_type)) in args.iter()
				.map(|arg| typecheck_expr(ctxt, funcs, arg))
				.zip(arg_type_list.iter())
				.enumerate(){
			let given_type = given_type?;
			let given_type_str = format!("{:?}", given_type);
			let given_type = decay_type(given_type);
			let correct_type: &ast::Ty = match correct_type {
				TypeVar(s) => if s == type_var_string {&type_var} else {
					panic!("argument {} to function {} has type '{}, which is not the type var the function was declared with.\
					This should have been detected when typechecking the function's declaration.")
				},
				t => &t
			};
			if given_type.ne(correct_type) {
				return Err(format!("argument {} to {} has type {}, expected {:?}", index, func_name, given_type_str, correct_type));
			}
		};
		Ok(false)
	},
	If(cond, then_block, else_block) => {
		let cond_type = typecheck_expr(ctxt, funcs, &cond)?;
		if cond_type != Bool {
			return Err(format!("condition of if statement must have type bool, not {:?}", cond_type));
		}
		let then_returns = typecheck_block(ctxt, funcs, then_block, expected_return_type)?;
		let else_returns = typecheck_block(ctxt, funcs, else_block, expected_return_type)?;
		Ok(then_returns && else_returns)
	},
	While(cond, body) => {
		let cond_type = typecheck_expr(ctxt, funcs, &cond)?;
		if cond_type != Bool {
			return Err(format!("condition of while statement must have type bool, not {:?}", cond_type));
		}
		let _ = typecheck_block(ctxt, funcs, body, expected_return_type)?;
		Ok(false)
	}
}
}

pub fn typecheck_block(ctxt: &mut LocalTypeContext, funcs: &FuncContext, block: &ast::Block, expected_return_type: &Option<ast::Ty>) -> Result<bool, String> {
	let mut stmt_returns = false;
	for stmt in block.iter(){
		if stmt_returns {
			return Err("definite return on statement that is not the last in a block".to_owned())
		}
		stmt_returns = typecheck_stmt(ctxt, funcs, stmt, expected_return_type)?;
	}
	Ok(stmt_returns)
}

pub fn typecheck_func_decl(ctxt: &mut LocalTypeContext, funcs: &FuncContext, name: String, args: &Vec<(ast::Ty, String)>, body: &ast::Block, ret_type: &Option<ast::Ty>) -> Result<(), String>{
	/*
	create a LocalTypeContext
	add all args to it as locals
	if ret_type is not None, make sure body definitely returns
	*/
	for (arg_ty, arg_name) in args.iter().cloned() {
		ctxt.locals.insert(arg_name, arg_ty);
	}
	let last_statement_definitely_returns = typecheck_block(ctxt, funcs, body, ret_type)?;
	if ret_type.is_some() && !last_statement_definitely_returns {
		return Err(format!("function '{}' might not return ", name));
	}
	Ok(())
	
}

pub fn typecheck_program(gdecls: Vec<ast::Gdecl>) -> Result<(), String>{
	/*
	create StructContext:
		collect names of all structs, put all of them into struct_context
			make sure a struct with this name does not already exist
		for each struct in struct_context:
			make sure there are no duplicate field
			make sure each field has a valid type
	create FuncContext:
	create GlobalContext:
		add builtins to a FuncContext
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
	for g in gdecls.iter().by_ref(){ match g {
		GStructDecl{name, fields} => {
			if struct_context.contains_key(name){
				return Err(format!("struct '{}' is declared more than once", name));
			}
			struct_context.insert(name.clone(), fields.iter().cloned().map(|(t, n)| {(n, t)}).collect());
		},
		GGenericFuncDecl{..} | GGenericStructDecl{..} => panic!("not supporting generics yet"),
		_ => ()
	}}
	//struct_context has been populated, now need to check for duplicate and invalid fields
	for (name, fields) in struct_context.iter(){
		let mut seen_fields: HashSet<&str> = HashSet::new();
		for (field_name, field_type) in fields.iter(){
			if seen_fields.contains(field_name.as_str()){
				return Err(format!("struct {} contains two fields named {}", name, field_name));
			}
			let temporary_generic_structs: HashMap<String, ()> = HashMap::new();
			all_struct_names_valid_map(field_type, &struct_context, &temporary_generic_structs)?;
			seen_fields.insert(field_name.as_str());
		}
	}

	let mut func_context: FuncContext = get_builtins();
	let mut global_context: GlobalContext = HashMap::new();
	global_context.insert("errno".to_owned(), ast::Ty::Int{signed: true, size: ast::IntSize::Size32});
	//TODO: figure out how builtins should be structured based on how other functions are added to func_context
	use ast::Gdecl::*;
	for g in gdecls.iter().by_ref(){ match g {
		GFuncDecl{ret_type, name: func_name, args, ..} => {
			if func_context.contains_key(func_name) {
				return Err(format!("function '{}' is declared more than once", func_name));
				//make sure generic funcs do not have any names in common with non-generic funcs
			}
			if global_context.contains_key(func_name) {
				return Err(format!("cannot declare a function named '{}', a global variable of that name already exists", func_name));
			}
			if let Some(ret) = ret_type{
				let temporary_generic_structs: HashMap<String, ()> = HashMap::new();
				all_struct_names_valid_map(&ret, &struct_context, &temporary_generic_structs)?;
			}
			let mut names: HashSet<String>  = HashSet::new();
			for (arg_type, arg_name) in args.iter().by_ref(){
				if names.contains(arg_name){
					return Err(format!("function '{}' contains two arguments both named '{}'", func_name, arg_name));
				}
				names.insert(arg_name.clone());
				let temporary_generic_structs: HashMap<String, ()> = HashMap::new();
				all_struct_names_valid_map(&arg_type, &struct_context, &temporary_generic_structs)?;
			}
			func_context.insert(func_name.clone(), FuncType::NonGeneric{
				return_type: ret_type.clone(),
				args: args.iter().cloned().map(|(t, _)| t).collect()
			});
		},
		//need to make sure there are no name collisions between global vars and functions
		GVarDecl(t, name) => {
			if global_context.contains_key(name) {
				return Err(format!("cannot have two global variables both named '{}'", name));
			}
			if func_context.contains_key(name) {
				return Err(format!("cannot declare global variable '{}', a function is already declared with that name", name));
			}
			global_context.insert(name.clone(), t.clone());
		},
		_ => ()
	}};
	for g in gdecls.iter().by_ref(){ match g {
		GFuncDecl{ret_type, name, args, body} => {
			let (mut ctxt, _) = get_empty_localtypecontext();
			typecheck_func_decl(&mut ctxt, &func_context, name.clone(), args, body, ret_type)?;
		},
		_ => ()
	}};
	Ok(())
}
