use crate::ast;
use std::collections::{HashMap};

struct FuncType{
	args: Vec<ast::Ty>,
	return_type: Option<ast::Ty>
}

type LocalContext = HashMap<String, ast::Ty>;
type GlobalContext = HashMap<String, ast::Ty>;
type StructContext = HashMap<String, Vec<(String, ast::Ty)>>;

pub struct TypeContext{
	locals: LocalContext,
	globals: GlobalContext,
	structs: StructContext,
	type_var: Option<(String, ast::PolymorphMode)>,
	type_for_lit_nulls: Option<ast::Ty>,
}

pub fn get_empty_typecontext() -> TypeContext{
	TypeContext{
		locals: HashMap::new(),
		globals: HashMap::new(),
		structs: HashMap::new(),
		type_var: None,
		type_for_lit_nulls: None
	}
}

pub fn typecheck_expr(ctxt: &mut TypeContext, e: &ast::Expr) -> Result<ast::Ty, String>{
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
		let first_type = typecheck_expr(ctxt, &init[0])?;
		for (index, init_expr) in init[1..].iter().enumerate() {
			let typ = typecheck_expr(ctxt, init_expr)?;
			if first_type.ne(&typ) {
				return Err(format!("Array literal has mismatching types, element 0 has type {:?}, element {} has type {:?}", first_type, index, typ));
			}
		}
		return Ok(Array{length: init.len() as u64, typ: Box::new(first_type)});
	},
	Index(base, index) => {
		let base_typ = typecheck_expr(ctxt, base)?;
		let result_type = match base_typ {
			Ptr(Some(typ)) | Array{typ, ..} => Ok(*typ),
			Ptr(None) => Err(format!("Can't index off of a void*")),
			_ => Err(format!("{:?} is not an array or pointer", base_typ))
		};
		if result_type.is_err() {
			return result_type;
		}
		let index_typ = typecheck_expr(ctxt, index)?;
		match index_typ {
			Int{..} => Ok(result_type.unwrap()),
			_ => Err(format!("Array indices must be integers, not {:?}", index_typ))
		}
	},
	Proj(base, field) => {
		let base_typ = typecheck_expr(ctxt, base)?;
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
	_ => Err("Not Implemented".to_owned())
}
}
