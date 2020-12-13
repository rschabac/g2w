use crate::ast;
use std::collections::{HashMap};

pub struct FuncType{
	pub args: Vec<ast::Ty>,
	pub return_type: Option<ast::Ty>
}

type LocalContext = HashMap<String, ast::Ty>;
type GlobalContext = HashMap<String, ast::Ty>;
type StructContext = HashMap<String, Vec<(String, ast::Ty)>>;
//TODO: complete type checker for regular structs, then see how StructContext is used,
//use this to figure out what GenericStructContext and GenericFuncContext should be
//type GenericStructContext = 
pub type FuncContext = HashMap<String, FuncType>;

pub struct LocalTypeContext{
	locals: LocalContext,
	globals: GlobalContext,
	structs: StructContext,
	type_var: Option<(String, ast::PolymorphMode)>,
	//TODO: one typechecking is done, find out when to set this
	type_for_lit_nulls: Option<ast::Ty>,
}

pub struct TypeContext{
	locals: LocalContext,
	globals: GlobalContext,
	structs: StructContext,
	funcs: FuncContext,
	type_var: Option<(String, ast::PolymorphMode)>,
	//TODO: one typechecking is done, find out when to set this
	type_for_lit_nulls: Option<ast::Ty>,
}

pub fn get_empty_typecontext() -> TypeContext{
	TypeContext{
		locals: HashMap::new(),
		globals: HashMap::new(),
		structs: HashMap::new(),
		funcs: HashMap::new(),
		type_var: None,
		type_for_lit_nulls: None
	}
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
			_ => Err(format!("{:?} is not a struct, project off of it", base_typ))
		}
	},
	Call(func_name, args) => {
		let return_type;
		let arg_type_list;
		let given_types = args.iter().map(|arg| typecheck_expr(ctxt, funcs, arg));
		match funcs.get(func_name) {
			None => {
				return Err(format!("could not find a function named '{}'", func_name));
			},
			Some(FuncType{return_type: None, ..}) => {
				return Err(format!("function '{}' returns void, cannot be used as an expression", func_name));
			},
			Some(FuncType{return_type: Some(ret), args: arg_types}) => {
				return_type = ret.clone();
				arg_type_list = arg_types;
			}
		};
		if args.len() != arg_type_list.len() {
			return Err(format!("wrong number of args to {}: given {} args, should be {}", func_name, args.len(), arg_type_list.len()));
		}
		for (index, (given_type, correct_type)) in given_types
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
	Binop(left, _bop, right) => {
		use ast::BinaryOp::*;
		let _left_type = typecheck_expr(ctxt, funcs, left)?;
		let _right_type = typecheck_expr(ctxt, funcs, right)?;
		panic!("todo")
		/*
		match bop {
			Add | Sub => match (left_type, right_type) {

			}
			_ => #[todo]
		}
		*/
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
