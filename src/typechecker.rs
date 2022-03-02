use std::collections::{HashMap, HashSet};
use crate::driver::Error;
use crate::ast2::*;


pub enum FuncType<'src: 'arena, 'arena>{
	NonGeneric{return_type: Option<&'arena Ty<'src, 'arena>>, args: &'arena [&'arena Ty<'src, 'arena>]},
	Generic{
		return_type: Option<&'arena Ty<'src, 'arena>>,
		mode: PolymorphMode,
		type_var: &'src str,
		args: &'arena [&'arena Ty<'src, 'arena>]
	}
}
pub enum StructType<'src: 'arena, 'arena>{
	NonGeneric(&'arena [(&'src str, &'arena Ty<'src, 'arena>)]),
	Generic{mode: PolymorphMode, type_var: &'src str, fields: &'arena [(&'src str, &'arena Ty<'src, 'arena>)]}
}

type LocalContext<'src, 'arena> = HashMap<&'src str, &'arena Ty<'src, 'arena>>;
type GlobalContext<'src, 'arena> = HashMap<&'src str, &'arena Ty<'src, 'arena>>;
pub type StructContext<'src, 'arena> = HashMap<&'src str, StructType<'src, 'arena>>;

//FuncContext contains generic and non-generic functions
//a generic and non-generic function cannot share the same name
pub type FuncContext<'src, 'arena> = HashMap<&'src str, FuncType<'src, 'arena>>;

pub struct LocalTypeContext<'src: 'arena, 'arena>{
	pub locals: LocalContext<'src, 'arena>,
	pub globals: GlobalContext<'src, 'arena>,
	pub structs: StructContext<'src, 'arena>,
	pub type_for_lit_nulls: Option<&'arena Ty<'src, 'arena>>,
	pub type_var: Option<(&'src str, PolymorphMode)>,
	pub is_lhs: bool,
}

pub fn get_empty_localtypecontext<'src: 'arena, 'arena>() -> (LocalTypeContext<'src, 'arena>, FuncContext<'src, 'arena>) {
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

pub fn replace_type_var_with<'src: 'arena, 'arena>(
		original: &'arena Ty<'src, 'arena>,
		type_var_str: &'src str,
		replacement: &'arena Ty<'src, 'arena>,
		typecache: &'arena TypeCache<'src, 'arena>)
		-> &'arena Ty<'src, 'arena> {
	use Ty::*;
	match original {
		TypeVar(s) => {
			debug_assert_eq!(s, &type_var_str, "When replacing '{}, found other type var '{}", type_var_str, s);
			replacement
		},
		Ptr(Some(t)) => {
			let replaced = replace_type_var_with(t, type_var_str, replacement, typecache);
			Ptr(Some(replaced)).getref(typecache)
		},
		Array{typ, length} => {
			let replaced = replace_type_var_with(typ, type_var_str, replacement, typecache);
			Array{typ: replaced, length: *length}.getref(typecache)
		},
		GenericStruct{type_param, name} => {
			let replaced = replace_type_var_with(type_param, type_var_str, replacement, typecache);
			GenericStruct{type_param: replaced, name}.getref(typecache)
		},
		Bool | Int{..} | Float(_) | Struct(_) | Ptr(None) => original
	}
}

//This function is called on all types that appear in the ast, and makes sure that any struct names
//are used appropriately, and that no erased type vars are passed to a separated struct or a
//separated function.
fn all_struct_names_valid<'src: 'arena, 'arena>(t: &Loc<&'arena Ty<'src, 'arena>>, struct_context: &StructContext<'src, 'arena>, current_type_var: &Option<(&'src str, PolymorphMode)>) -> Result<(), Error> {
	fn recursively_check<'src: 'arena, 'arena>(t: &'arena Ty<'src, 'arena>, struct_context: &StructContext<'src, 'arena>, current_type_var: &Option<(&'src str, PolymorphMode)>) -> Result<(), String> {
		use Ty::*;
		use StructType::*;
		match t {
		Struct(s) => match struct_context.get(s) {
			None => Err(format!("struct {} does not exist", s)),
			Some(Generic{..}) => Err(format!("struct {} is generic", s)),
			Some(NonGeneric(_)) => Ok(())
		},
		GenericStruct{name, type_param} => match struct_context.get(name) {
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
						if current_var != &s {
							return Err(format!("Cannot pass unknown type variable '{} to struct {}", current_var, name));
						}
						//cannot pass an erased type var to a separated struct
						if *current_mode == PolymorphMode::Erased && *mode == PolymorphMode::Separated {
							return Err(format!("Cannot pass erased type variable '{} to separated struct {}", s, name));
						}
					}
					_ => ()
				};
				recursively_check(type_param, struct_context, current_type_var)
			}
		},
		Ptr(Some(t)) | Array{typ: t, ..} => recursively_check(t, struct_context, current_type_var),
		_ => Ok(())
		}
	}
	if let Err(errmsg) = recursively_check(t.elt, struct_context, current_type_var) {
		Err(Error{
			err: errmsg,
			byte_offset: t.byte_offset,
			approx_len: t.byte_len,
			file_id: t.file_id
		})
	} else {
		Ok(())
	}
}


//Is this the best place to put the indirection in exprs?
pub fn typecheck_expr<'src: 'arena, 'arena: 'expr + 'ctxt, 'expr, 'ctxt>(
	ctxt: &'ctxt mut LocalTypeContext<'src, 'arena>,
	funcs: &FuncContext<'src, 'arena>,
	e: &'expr mut Loc<TypedExpr<'src, 'arena>>,
	typecache: &'arena TypeCache<'src, 'arena>) -> Result<(), Vec<Error>>{
use Ty::*;
use Expr::*;
use IntSize::*;
match &mut e.elt.expr {
	LitNull => match &ctxt.type_for_lit_nulls {
		Some(t @ Ptr(_)) => {
			e.elt.typ = Some(t);
			Ok(())
		},
		Some(t) => Err(vec![Error{
			err: format!("Cannot make null literal have type {} (it is not a pointer)", t),
			byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
		}]),
		None => Err(vec![Error{
			err: "Cannot infer type of null literal".to_owned(),
			byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
		}])
	},
	LitBool(_) => {
		e.elt.typ = Some(Bool.getref(typecache));
		Ok(())
	},
	LitSignedInt(_, size) => {
		e.elt.typ = Some(Int{signed: true, size: *size}.getref(typecache));
		Ok(())
	},
	LitUnsignedInt(_, size) => {
		e.elt.typ = Some(Int{signed: false, size: *size}.getref(typecache));
		Ok(())
	},
	LitFloat(_, size) => {
		e.elt.typ = Some(Float(*size).getref(typecache));
		Ok(())
	},
	LitString(_) => {
		let u8_typ = Int{signed: false, size: Size8}.getref(typecache);
		let u8_ptr_typ = Ptr(Some(u8_typ)).getref(typecache);
		e.elt.typ = Some(u8_ptr_typ);
		Ok(())
	},
	Id(var) => match ctxt.locals.get(var) {
			Some(t) => {
				e.elt.typ = Some(t);
				Ok(())
			},
			None => match ctxt.globals.get(var) {
				Some(t) => {
					e.elt.typ = Some(t);
					Ok(())
				},
				None => Err(vec![Error{
					err: format!("Undeclared variable {}", var),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}])
		}
	},
	Index(base, index) => {
		ctxt.type_for_lit_nulls = None;
		let mut errors = Vec::new();
		let result_type = if let Err(mut base_errors) = typecheck_expr(ctxt, funcs, base, typecache) {
			errors.append(&mut base_errors);
			None
		} else {
			match base.elt.typ.as_mut().unwrap() {
				Ptr(Some(typ)) => Some(typ),
				Array{typ, ..} => if !matches!(base.elt.expr, Expr::Id(_) | Expr::Index(_,_) | Expr::Proj(_,_) | Expr::Deref(_)) {
					errors.push(Error{
						err: "Cannot index off of something of array type that is not an lvalue".to_owned(),
						byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
					});
					None
				} else {
					Some(typ)
				},
				Ptr(None) => {
					errors.push(Error{
						err: "Cannot index off of a void*".to_owned(),
						byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
					});
					None
				},
				other => {
					errors.push(Error{
						err: format!("Cannot index off of type {}, it is not an array or pointer", other),
						byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
					});
					None
				}
			}
		};
		if let Err(mut index_errors) = typecheck_expr(ctxt, funcs, index, typecache) {
			errors.append(&mut index_errors);
		} else {
			match index.elt.typ.as_mut().unwrap() {
				Int{..} => (),
				other => errors.push(Error{
					err: format!("Indices must be integers, not {}", other),
					byte_offset: index.byte_offset, approx_len: index.byte_len, file_id: index.file_id
				})
			}
		}
		if errors.is_empty() {
			e.elt.typ = Some(result_type.unwrap());
			Ok(())
		} else {
			Err(errors)
		}
	},
	Proj(base, field) => {
		use StructType::*;
		//if base is LitNull, I can't determine what struct it is
		ctxt.type_for_lit_nulls = None;
		//if the base has a type error, I can't check anything else about this Proj
		typecheck_expr(ctxt, funcs, base, typecache)?;
		let base_typ = base.elt.typ.unwrap();
		match base_typ {
			Ptr(Some(nested)) => match nested {
				Struct(struct_name) => match ctxt.structs.get(struct_name) {
					None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
					Some(NonGeneric(field_list)) => {
						for (field_name, typ) in field_list.iter() {
							if field.elt.eq(*field_name) {
								e.elt.typ = Some(typ);
								return Ok(());
							}
						}
						Err(vec![Error{
							err: format!("struct {} does not have a .{} field", struct_name, field),
							byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
						}])
					},
					Some(Generic{..}) => panic!("Proj: base had type {}, but struct context contained a generic struct for {}", base_typ, struct_name)
				},
				GenericStruct{type_param, name: struct_name} => match ctxt.structs.get(struct_name) {
					None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
					Some(NonGeneric(_)) => panic!("Proj: base had type {}, but struct context contained a non-generic struct for {}", base_typ, struct_name),
					Some(Generic{mode: _, type_var, fields}) => {
						for (field_name, typ) in fields.iter() {
							if field.elt.eq(*field_name) {
								let replaced_ty = replace_type_var_with(typ, type_var, type_param, typecache);
								e.elt.typ = Some(replaced_ty);
								return Ok(());
							}
						}
						Err(vec![Error{
							err: format!("struct {} does not have a .{} field", struct_name, field),
							byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
						}])
					}
				},
				other => Err(vec![Error{
					err: format!("{} is not a struct or pointer to a struct, cannot project off of it", other),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}])
			},
			Struct(struct_name) => match ctxt.structs.get(struct_name) {
				None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
				Some(NonGeneric(field_list)) => {
					/*
					if is_lhs is set and base is not a pointer and base itself is not an lvalue, error
					*/
					let mut errors = Vec::new();
					if ctxt.is_lhs && !matches!(&base.elt.expr, Id(_) | Index(_,_) | Proj(_,_) | Deref(_)){
						errors.push(Error{
							err: "Cannot assign to field of struct that is not an lvalue".to_owned(),
							byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
						})
					}
					for (field_name, typ) in field_list.iter() {
						if field.elt.eq(*field_name) {
							if errors.is_empty() {
								//e.elt.typ = Some(replace_type_var_with(typ, type_var, type_param))
								e.elt.typ = Some(typ);
								return Ok(());
							} else {
								return Err(errors);
							}
						}
					}
					errors.push(Error{
						err: format!("struct {} does not have a .{} field", struct_name, field),
						byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
					});
					Err(errors)
				},
				Some(Generic{..}) => panic!("Proj: base type was {}, but struct context contained a generic struct", base_typ)
			},
			GenericStruct{type_param, name: struct_name} => match ctxt.structs.get(struct_name) {
				None => panic!("Proj: base had type {}, but struct context did not contain an entry for '{}'", base_typ, struct_name),
				Some(NonGeneric(_)) => panic!("Proj: base had type {}, but struct context contained a non-generic struct for {}", base_typ, struct_name),
				Some(Generic{mode: _, type_var, fields}) => {
					/*
					if is_lhs is set and base is not a pointer and base itself is not an lvalue, error
					*/
					let mut errors = Vec::new();
					if ctxt.is_lhs && !matches!(&base.elt.expr, Id(_) | Index(_,_) | Proj(_,_) | Deref(_)){
						errors.push(Error{
							err: "Cannot assign to field of struct that is not an lvalue".to_owned(),
							byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
						})
					}
					for (field_name, typ) in fields.iter() {
						if field.elt.eq(*field_name) {
							if errors.is_empty() {
								e.elt.typ = Some(replace_type_var_with(typ, type_var, type_param, typecache));
								//e.elt.typ = Some(typ);
								return Ok(());
							} else {
								return Err(errors);
							}
						}
					}
					errors.push(Error{
						err: format!("struct {} does not have a .{} field", struct_name, field),
						byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
					});
					Err(errors)
				}
			},
			other => Err(vec![Error{
				err: format!("{} is not a struct or pointer to a struct, cannot project off of it", other),
				byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
			}])
		}
	},
	Call(func_name, args) => {
		use FuncType::*;
		if PRINTF_FAMILY.contains(&func_name.elt){
			typecheck_printf(func_name.elt, args, ctxt, funcs, e.byte_offset, e.byte_len, e.file_id, typecache)?;
			e.elt.typ = Some(Int{signed: true, size: IntSize::Size32}.getref(typecache));
			return Ok(());
		}
		let return_type;
		let arg_type_list;
		match funcs.get(func_name.elt) {
			None => {
				return Err(vec![Error{
					err: format!("Could not find a function named '{}'", func_name),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}]);
			},
			Some(NonGeneric{return_type: None, ..}) => {
				return Err(vec![Error{
					err: format!("Function '{}' returns void, cannot be used as an expression", func_name),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}]);
			},
			Some(Generic{..}) => {
				return Err(vec![Error{
					err: format!("Function '{}' is generic", func_name),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}]);
			},
			Some(NonGeneric{return_type: Some(ret), args: arg_types}) => {
				return_type = ret;
				arg_type_list = arg_types;
			}
		};
		let mut errors = Vec::new();
		let mut check_against_expected_types = true;
		if args.len() != arg_type_list.len() {
			errors.push(Error{
				err: format!("Wrong number of args to {}: given {} args, should be {}", func_name.elt, args.len(), arg_type_list.len()),
				byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
			});
			check_against_expected_types = false;
		}
		for (index, (arg, correct_type)) in args.iter_mut().zip(arg_type_list.iter()).enumerate() {
			ctxt.type_for_lit_nulls = Some(correct_type);
			if let Err(mut errs) = typecheck_expr(ctxt, funcs, arg, typecache) {
				errors.append(&mut errs);
			} else if check_against_expected_types && arg.elt.typ.unwrap().ne(correct_type) {
				errors.push(Error{
					err: format!("Argument {} to {} has type {}, expected {}", index + 1, func_name.elt, arg.elt.typ.unwrap(), correct_type),
					byte_offset: arg.byte_offset, approx_len: arg.byte_len, file_id: arg.file_id
				})
			}
		}
		if errors.is_empty() {
			e.elt.typ = Some(return_type);
			Ok(())
		} else {
			Err(errors)
		}
	},
	GenericCall{name: func_name, type_param, args} => {
		use FuncType::*;
		let mut errors = Vec::new();
		let mut type_param_was_valid = true;
		if let Err(err) = all_struct_names_valid(type_param, &ctxt.structs, &ctxt.type_var) {
			errors.push(err);
			type_param_was_valid = false;
		}
		let return_type;
		let arg_type_list;
		let callee_mode;
		let type_var_string;
		match funcs.get(func_name.elt) {
			None => {
				errors.push(Error{
					err: format!("Could not find a function named '{}'", func_name.elt),
					byte_offset: func_name.byte_offset, approx_len: func_name.byte_len, file_id: func_name.file_id
				});
				return Err(errors);
			},
			Some(Generic{return_type: None, ..}) => {
				errors.push(Error{
					err: format!("Function '{}' returns void, cannot be used as an expression", func_name),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				});
				return Err(errors);
			},
			Some(NonGeneric{..}) => {
				errors.push(Error{
					err: format!("Function '{}' is not generic", func_name),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				});
				return Err(errors);
			},
			Some(Generic{return_type: Some(ret), mode, type_var: var_string, args: arg_types}) => {
				return_type = ret;
				arg_type_list = arg_types;
				callee_mode = mode;
				type_var_string = var_string;
			}
		};
		let mut check_against_expected_types = true;
		let type_var_str_in_type_var = type_param.elt.recursively_find_type_var();
		match (type_var_str_in_type_var, &ctxt.type_var) {
			(None, _) => (),
			(Some(s), None) => {
				errors.push(Error{
					err: format!("Cannot use type variable '{} in non-generic function", s),
					byte_offset: type_param.byte_offset, approx_len: type_param.byte_len, file_id: type_param.file_id
				});
			},
			(Some(s), Some((current_func_type_var, current_func_mode))) => {
				if &s != current_func_type_var {
					errors.push(Error{
						err: format!("Type param passed to generic func {} contains unknown type variable '{}", func_name, s),
						byte_offset: type_param.byte_offset, approx_len: type_param.byte_len, file_id: type_param.file_id
					});
				}
				use PolymorphMode::*;
				if *callee_mode == Separated && *current_func_mode == Erased {
					errors.push(Error{
						err: format!("Cannot call separated function {} from erased function", func_name),
						byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
					});
				}
			}
		};
		if args.len() != arg_type_list.len() {
			errors.push(Error{
				err: format!("Wrong number of args to {}: given {} args, should be {}", func_name.elt, args.len(), arg_type_list.len()),
				byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
			});
			check_against_expected_types = false;
		}
		/*
		expr is:		name@<type_param>(..args..)
		name has type:	return_type name@<var_string>(..arg_type_list..)
		the monomorphed version of name would look like:
						return_type name_mangled_type_var(..arg_type_list with var_string replaced with type_var..)
		*/
		for (index, (arg, correct_type)) in args.iter_mut().zip(arg_type_list.iter()).enumerate() {
			//if the type param of this call was not valid, don't try to do any replacements
			//instead, just skip typechecking on any arg where a replacement would take place
			let replaced_type = replace_type_var_with(correct_type, type_var_string, type_param.elt, typecache);
			if !type_param_was_valid && &replaced_type != correct_type {
				continue;
			}
			ctxt.type_for_lit_nulls = Some(replaced_type);
			if let Err(mut errs) = typecheck_expr(ctxt, funcs, arg, typecache) {
				errors.append(&mut errs);
			} else if check_against_expected_types && arg.elt.typ.unwrap().ne(replaced_type) {
				errors.push(Error{
					err: format!("Argument {} to {} has type {}, expected {}", index + 1, func_name.elt, arg.elt.typ.unwrap(), correct_type),
					byte_offset: arg.byte_offset, approx_len: arg.byte_len, file_id: arg.file_id
				})
			}
		}
		/*
		current context type var is 'A
		expr is func_name@<type_param which contains 'A>(..args..)
		func_name is declared with type return_type func_name@<(erased|separated) 'C>(..arg_type_list..)
		this expr has type (return_type with 'C replaced with type_param)
		*/
		if errors.is_empty() {
			let replaced_type_var = replace_type_var_with(return_type, type_var_string, type_param.elt, typecache);
			e.elt.typ = Some(replaced_type_var);
			Ok(())
		} else {
			Err(errors)
		}
	},
	Cast(dest_type, source) => {
		let mut errors = Vec::new();
		if let Err(err) = all_struct_names_valid(dest_type, &ctxt.structs, &ctxt.type_var) {
			errors.push(err);
		}
		let type_var_str_in_dest_type = dest_type.recursively_find_type_var();
		match (type_var_str_in_dest_type, &ctxt.type_var) {
			(Some(s), None) => {
				errors.push(Error{
					err: format!("Cannot use type var '{} in non-generic function", s),
					byte_offset: dest_type.byte_offset, approx_len: dest_type.byte_len, file_id: dest_type.file_id
				});
			},
			(Some(s), Some((current_func_type_var, _))) if &s != current_func_type_var => {
				errors.push(Error{
					err: format!("Type used in cast contains unknown type var '{}", s),
					byte_offset: dest_type.byte_offset, approx_len: dest_type.byte_len, file_id: dest_type.file_id
				});
			},
			_ => ()
		};
		ctxt.type_for_lit_nulls = Some(&Ptr(None));
		//if the base expr has a type error, just assume that the cast works
		match typecheck_expr(ctxt, funcs, source, typecache) {
			Err(mut errs) => {
				errors.append(&mut errs);
				e.elt.typ = Some(dest_type.elt);
				return Ok(());
			},
			Ok(()) => ()
		};
		match (source.elt.typ.unwrap(), dest_type.elt) {
			(Int{..}, Int{..})
		  | (Ptr(_), Ptr(_))
		  | (Float(_), Float(_))
		  | (Float(_), Int{..}) | (Int{..}, Float(_))
		  | (Bool, Int{..}) => (),
			(TypeVar(v), _) => {
				errors.push(Error{
					err: format!("Cannot cast from '{}", v),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			(_, TypeVar(v)) => {
				errors.push(Error{
					err: format!("Cannot cast to '{}", v),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			(original_type, dest_type) => {
				errors.push(Error{
					err: format!("Cannot cast from {} to {}", original_type, dest_type),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			}
		};
		if errors.is_empty() {
			e.elt.typ = Some(dest_type.elt);
			Ok(())
		} else {
			Err(errors)
		}
	},
	Binop(left, bop, right) => {
		use BinaryOp::*;
		let mut errors = Vec::new();
		ctxt.type_for_lit_nulls = Some(&Ptr(None));
		if let Err(mut errs) = typecheck_expr(ctxt, funcs, left, typecache) {
			errors.append(&mut errs);
		}
		ctxt.type_for_lit_nulls = Some(&Ptr(None));
		if let Err(mut errs) = typecheck_expr(ctxt, funcs, right, typecache) {
			errors.append(&mut errs);
		}
		if !errors.is_empty() {
			return Err(errors);
		}
		let result_ty_or_err = match bop {
			Add | Sub => match (left.elt.typ.unwrap(), right.elt.typ.unwrap()) {
				(original @ Ptr(_), Int{..}) => Ok(original),
				//TODO: this restriction is unnecessary, check if bop is Sub, then update frontend
				(Int{..}, Ptr(_)) => Err(Error{
					err: "when doing pointer arithmetic, the pointer must be the left hand side, and the integer must be the right hand side".to_owned(),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}),
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: *sign1, size: if size1 > size2 {*size1} else {*size2}}.getref(typecache)),
				(Int{..}, Int{..}) => Err(Error{
					err: format!("Cannot {} integers with different signedness", if *bop == Add {"add"} else {"subtract"}),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}),
				(Float(size1), Float(size2)) => Ok(Float(if size1 > size2 {*size1} else {*size2}).getref(typecache)),
				(left_type, right_type) => Err(Error{
					err: format!("Cannot {} types {} and {}", if *bop == Add {"add"} else {"subtract"}, left_type, right_type),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			Mul | Div | Mod => match (left.elt.typ.unwrap(), right.elt.typ.unwrap()) {
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: *sign1, size: if size1 > size2 {*size1} else {*size2}}.getref(typecache)),
				(Int{..}, Int{..}) => Err(Error{
					err: format!("Cannot {} integers with different signedness", match bop {Mul => "multiply", Div => "divide", Mod => "mod", _ => unreachable!()}),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}),
				(Float(size1), Float(size2)) => Ok(Float(if size1 > size2 {*size1} else {*size2}).getref(typecache)),
				(left_type, right_type) => Err(Error{
					err: format!("Cannot {} types {} and {}", match bop {Mul => "multiply", Div => "divide", Mod => "mod", _ => unreachable!()}, left_type, right_type),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			Lt | Lte | Gt | Gte | Equ | Neq => match (left.elt.typ.unwrap(), right.elt.typ.unwrap()) {
				(Int{signed: sign1,..}, Int{signed: sign2,..}) if sign1 != sign2 => Err(Error{
					err: "Cannot compare signed and unsigned int".to_owned(),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}),
				(Int{..}, Int{..}) | (Float(_), Float(_)) | (Bool, Bool) => Ok(Bool.getref(typecache)),
				(Ptr(p1), Ptr(p2)) if p1 == p2 => Ok(Bool.getref(typecache)),
				(left_type, right_type) => Err(Error{
					err: format!("Cannot compare types {} and {}", left_type, right_type),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			And | Or => match (left.elt.typ.unwrap(), right.elt.typ.unwrap()) {
				(Bool, Bool) => Ok(Bool.getref(typecache)),
				(left_type, right_type) => Err(Error{
					err: format!("Logical {} cannot be applied to types {} and {}", if *bop == And {"and"} else {"or"}, left_type, right_type),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			Bitand | Bitor | Bitxor => match (left.elt.typ.unwrap(), right.elt.typ.unwrap()) {
				(Int{signed: sign1, size: size1}, Int{signed: sign2, size: size2}) if sign1 == sign2 => Ok(Int{signed: *sign1, size: if size1 > size2 {*size1} else {*size2}}.getref(typecache)),
				(left_type, right_type) => Err(Error{
					err: format!("Bitwise {} cannot be applied to types {} and {}", match bop {Bitand => "and", Bitor => "or", Bitxor => "xor", _ => unreachable!()}, left_type, right_type),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			Shl | Shr | Sar => match (left.elt.typ.unwrap(), right.elt.typ.unwrap()) {
				(left_type @ Int{..}, Int{..}) => Ok(left_type),
				(left_type, right_type) => Err(Error{
					err: format!("Cannot bitshift {} by {}", left_type, right_type),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			}
		};
		match result_ty_or_err {
			Ok(ty) => {
				e.elt.typ = Some(ty);
				Ok(())
			},
			Err(e) => Err(vec![e])
		}
	},
	Unop(op, inner) => {
		use UnaryOp::*;
		ctxt.type_for_lit_nulls = Some(&Ptr(None));
		typecheck_expr(ctxt, funcs, inner, typecache)?; 
		let inner_typ = inner.elt.typ.unwrap();
		let result_ty_or_err = match op {
			Neg => match inner_typ {
				Int{signed: true, ..} | Float(_) => Ok(inner_typ),
				Int{signed: false, ..} => Err(Error{
					err: "Cannot negate an unsigned integer".to_owned(),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				}),
				other => Err(Error{
					err: format!("Cannot negate type {}", other),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			Lognot => match inner_typ {
				Bool => Ok(Bool.getref(typecache)),
				other => Err(Error{
					err: format!("Logical not can only be applied to bool, not {}", other),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			},
			Bitnot => match inner_typ {
				Int{..} => Ok(inner_typ),
				other => Err(Error{
					err: format!("Bitwise not can only be applied to integers, not {}", other),
					byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
				})
			}
		};
		match result_ty_or_err {
			Ok(result_ty) => {
				e.elt.typ = Some(result_ty);
				Ok(())
			},
			Err(err) => Err(vec![err])
		}
	},
	GetRef(inner) => {
		let mut errors = Vec::new();
		if let Err(mut errs) = typecheck_expr(ctxt, funcs, inner, typecache) {
			errors.append(&mut errs);
		}
		//don't need to set type_for_lit_nulls here because it will already be an error anyway
		if !matches!(&inner.elt.expr, Id(_) | Proj(_,_) | Index(_,_) | Deref(_)) {
			errors.push(Error{
				err: "Cannot get address of expression".to_owned(),
				byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
			});
		}
		if errors.is_empty() {
			e.elt.typ = Some(Ptr(Some(inner.elt.typ.unwrap())).getref(typecache));
			Ok(())
		} else {
			Err(errors)
		}
	},
	Deref(inner) => {
		ctxt.type_for_lit_nulls = Some(&Ptr(None));
		typecheck_expr(ctxt, funcs, inner, typecache)?;
		match inner.elt.typ.unwrap() {
			Ptr(Some(t)) => {
				e.elt.typ = Some(t);
				Ok(())
			},
			other => Err(vec![Error{
				err: format!("Cannot dereference type {}", other),
				byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
			}])
		}
	},
	Sizeof(t) => {
		if let Err(err) = all_struct_names_valid(t, &ctxt.structs, &ctxt.type_var) {
			return Err(vec![err])
		}
		let type_var_str_in_type = t.recursively_find_type_var();
		match (type_var_str_in_type, &ctxt.type_var) {
			(Some(s), None) => Err(vec![Error{
				err: format!("Cannot use type variable '{} in non-generic function", s),
				byte_offset: t.byte_offset, approx_len: t.byte_len, file_id: t.file_id
			}]),
			(Some(s), Some((current_func_type_var, _))) if &s != current_func_type_var => Err(vec![Error{
				err: format!("Type contains unknown type variable '{}", s),
				byte_offset: t.byte_offset, approx_len: t.byte_len, file_id: t.file_id
			}]),
			_ => {
				e.elt.typ = Some(Int{signed: false, size: Size64}.getref(typecache));
				Ok(())
			}
		}
	}
}
}

//when typechecking a function call, it the function is one of these, the
//number and type of arguments are not checked (each individual argument must
//still be well-typed though).
pub const PRINTF_FAMILY: &[&str] = &[
	"printf",
	"sprintf",
	//"fprintf", //this requires a FILE*, which will require c header files to define
	"snprintf",
	"dprintf"
];

#[allow(clippy::too_many_arguments)]
fn typecheck_printf<'src: 'arena, 'arena: 'ctxt + 'expr, 'expr, 'ctxt>(
	func_name: &'src str,
	args: &'expr mut [Loc<TypedExpr<'src, 'arena>>],
	ctxt: &'ctxt mut LocalTypeContext<'src, 'arena>,
	funcs: &FuncContext<'src, 'arena>,
	byte_offset: usize, byte_len: usize, file_id: u16,
	typecache: &'arena TypeCache<'src, 'arena>) -> Result<(), Vec<Error>> {
	/*
	According to the C standard, there is something called "default argument promotion" that happens when the expected type
	of the argument is unknown (such as when passing arguments to printf). This means that floats are converted to doubles,
	and chars, shorts, and enums are converted to int (probably int, maybe even long). Ideally, I could do this myself in
	the frontend, but for now, I will just give an error when the arguments to printf are one of these shorter types.
	*/
	use Ty::*;
	use IntSize::*;
	use FloatSize::*;
	let mut errors = Vec::new();
	let starting_index: usize; //index of first variadic param in args
	match func_name {
		"printf" => {
			if args.is_empty() {
				errors.push(Error{
					err: "printf requires at least one argument".to_owned(),
					byte_offset, approx_len: byte_len, file_id
				});
			} else if let Err(mut errs) = typecheck_expr(ctxt, funcs, &mut args[0], typecache) {
				errors.append(&mut errs);
			} else if args[0].elt.typ.unwrap() != &Ptr(Some(&Int{size: Size8, signed: false})) {
				errors.push(Error{
					err: "The first argument to printf must be a u8*".to_owned(),
					byte_offset: args[0].byte_offset, approx_len: args[0].byte_len, file_id: args[0].file_id
				});
			}
			starting_index = 1;
		},
		"sprintf" => {
			if args.len() < 2 {
				errors.push(Error{
					err: "sprintf requires at least two arguments".to_owned(),
					byte_offset, approx_len: byte_len, file_id
				});
			}
			if !args.is_empty() {
				if let Err(mut errs) = typecheck_expr(ctxt, funcs, &mut args[0], typecache) {
					errors.append(&mut errs);
				} else if args[0].elt.typ.unwrap() != &Ptr(Some(&Int{size: Size8, signed: false})) {
					errors.push(Error{
						err: "The first argument to sprintf must be a u8*".to_owned(),
						byte_offset: args[0].byte_offset, approx_len: args[0].byte_len, file_id: args[0].file_id
					});
				}
				if args.len() >= 2 {
					if let Err(mut errs) = typecheck_expr(ctxt, funcs, &mut args[1], typecache) {
						errors.append(&mut errs);
					} else if args[1].elt.typ.unwrap() != &Ptr(Some(&Int{size: Size8, signed: false})) {
						errors.push(Error{
							err: "The second argument to sprintf must be a u8*".to_owned(),
							byte_offset: args[1].byte_offset, approx_len: args[1].byte_len, file_id: args[1].file_id
						});
					}
				}
			}
			starting_index = 2;
		},
		"snprintf" => {
			if args.len() < 3 {
				errors.push(Error{
					err: "snprintf requires at least three arguments".to_owned(),
					byte_offset, approx_len: byte_len, file_id
				});
			}
			if !args.is_empty() {
				if let Err(mut errs) = typecheck_expr(ctxt, funcs, &mut args[0], typecache) {
					errors.append(&mut errs);
				} else if args[0].elt.typ.unwrap() != &Ptr(Some(&Int{size: Size8, signed: false})) {
					errors.push(Error{
						err: "The first argument to snprintf must be a u8*".to_owned(),
						byte_offset: args[0].byte_offset, approx_len: args[0].byte_len, file_id: args[0].file_id
					});
				}
				if args.len() >= 2 {
					if let Err(mut errs) = typecheck_expr(ctxt, funcs, &mut args[1], typecache) {
						errors.append(&mut errs);
					} else if args[1].elt.typ.unwrap() != &(Int{signed: false, size: Size64}) {
						errors.push(Error{
							err: "The second argument to snprintf must be a u64".to_owned(),
							byte_offset: args[1].byte_offset, approx_len: args[1].byte_len, file_id: args[1].file_id
						});
					}
					if args.len() >= 3 {
						if let Err(mut errs) = typecheck_expr(ctxt, funcs, &mut args[2], typecache) {
							errors.append(&mut errs);
						} else if args[2].elt.typ.unwrap() != &Ptr(Some(&Int{size: Size8, signed: false})) {
							errors.push(Error{
								err: "The third argument to snprintf must be a u8*".to_owned(),
								byte_offset: args[2].byte_offset, approx_len: args[2].byte_len, file_id: args[2].file_id
							});
						}
					}
				}
			}
			starting_index = 3;
		},
		"dprintf" => {
			if args.len() < 2 {
				errors.push(Error{
					err: "dprintf requires at least two arguments".to_owned(),
					byte_offset, approx_len: byte_len, file_id
				});
			}
			if !args.is_empty() {
				if let Err(mut errs) = typecheck_expr(ctxt, funcs, &mut args[0], typecache) {
					errors.append(&mut errs);
				} else if args[0].elt.typ.unwrap() != &(Int{size: Size32, signed: true}) {
					errors.push(Error{
						err: "The first argument to dprintf must be a i32".to_owned(),
						byte_offset: args[0].byte_offset, approx_len: args[0].byte_len, file_id: args[0].file_id
					});
				}
				if args.len() >= 2 {
					if let Err(mut errs) = typecheck_expr(ctxt, funcs, &mut args[1], typecache) {
						errors.append(&mut errs);
					} else if args[1].elt.typ.unwrap() != &Ptr(Some(&Int{size: Size8, signed: false})) {
						errors.push(Error{
							err: "The second argument to dprintf must be a u8*".to_owned(),
							byte_offset: args[1].byte_offset, approx_len: args[1].byte_len, file_id: args[1].file_id
						});
					}
				}
			}
			starting_index = 2;
		},
		_ => panic!("typecheck_printf called with non-printf function {} (maybe it's just not in PRINT_FAMILY)", func_name)
	};
	for (i, arg) in args[starting_index..].iter_mut().enumerate().map(|(i, e)| (i + starting_index, e)) {
		if let Err(mut errs) = typecheck_expr(ctxt, funcs, arg, typecache) {
			errors.append(&mut errs);
			continue
		}
		let arg_ty = arg.elt.typ.unwrap();
		let correction: Option<(&str, &str)> = match arg_ty {
			Float(FSize32) => Some(("f32", "f64")),
			Int{size: Size8, signed: true} => Some(("i8", "i32")),
			Int{size: Size8, signed: false} => Some(("u8", "u32")),
			Int{size: Size16, signed: true} => Some(("i16", "i32")),
			Int{size: Size16, signed: false} => Some(("u16", "u32")),
			_ => None
		};
		if let Some((bad, good)) = correction {
			errors.push(Error{
				err: format!("{} argument {} must be manually promoted from {} to {}", func_name, i + 1, bad, good),
				byte_offset: arg.byte_offset, approx_len: arg.byte_len, file_id: arg.file_id
			});
		}
	};
	if errors.is_empty() {
		Ok(())
	} else {
		Err(errors)
	}
}

pub fn typecheck_stmt<'src: 'arena, 'arena: 'stmt, 'stmt>(
		ctxt: &mut LocalTypeContext<'src, 'arena>,
		funcs: &FuncContext<'src, 'arena>,
		s: &'stmt mut Loc<Stmt<'src, 'arena>>,
		expected_return_type: Option<&'arena Ty<'src, 'arena>>,
		typecache: &'arena TypeCache<'src, 'arena>)
		-> Result<bool, Vec<Error>> {
use Ty::*;
use Expr::*;
use Stmt::*;
match &mut s.elt {
	Assign(lhs, rhs) => {
		let mut errors = Vec::new();
		let lhs_typ: Option<&'arena Ty<'src, 'arena>> = match &lhs.elt.expr {
			Id(_) | Index(_,_) | Proj(_,_) | Deref(_) => {
				ctxt.is_lhs = true;
				let expr_result = typecheck_expr(ctxt, funcs, lhs, typecache);
				ctxt.is_lhs = false;
				if let Err(mut errs) = expr_result {
					errors.append(&mut errs);
					None
				} else {
					debug_assert!(lhs.elt.typ.is_some());
					lhs.elt.typ
				}
			},
			_ => {
				errors.push(Error{
					err: "Left-hand-side of assignment is not an assignable expression".to_owned(),
					byte_offset: lhs.byte_offset, approx_len: lhs.byte_len, file_id: lhs.file_id
				});
				None
			}
		};
		let rhs_typ = {
			ctxt.type_for_lit_nulls = lhs_typ;
			if let Err(mut errs) = typecheck_expr(ctxt, funcs, rhs, typecache) {
				errors.append(&mut errs);
				None
			} else {
				debug_assert!(rhs.elt.typ.is_some());
				rhs.elt.typ
			}
		};
		if let (Some(lhs_typ), Some(rhs_typ)) = (lhs_typ, rhs_typ) {
			if lhs_typ != rhs_typ {
				errors.push(Error{
					err: format!("Cannot assign value of type {} to something of type {}", rhs_typ, lhs_typ),
					byte_offset: s.byte_offset, approx_len: s.byte_len, file_id: s.file_id
				})
			}
		};
		if errors.is_empty() {
			Ok(false)
		} else {
			Err(errors)
		}
	},
	Decl(typ, name) => {
		let mut errors = Vec::new();
		if let Err(err) = all_struct_names_valid(typ, &ctxt.structs, &ctxt.type_var) {
			errors.push(err);
		}
		let type_var_str_in_decl_type = typ.recursively_find_type_var();
		match (type_var_str_in_decl_type, &ctxt.type_var) {
			(Some(s), None) => {
				errors.push(Error{
					err: format!("Cannot use type var '{} in non-generic function", s),
					byte_offset: typ.byte_offset, approx_len: typ.byte_len, file_id: typ.file_id
				});
			},
			(Some(s), Some((current_func_type_var, _))) if &s != current_func_type_var => {
				errors.push(Error{
					err: format!("Type used in declaration of {} contains unknown type var '{}", name, s),
					byte_offset: typ.byte_offset, approx_len: typ.byte_len, file_id: typ.file_id
				});
			},
			_ => ()
		};
		if ctxt.locals.contains_key(name.elt){
			errors.push(Error{
				err: format!("redeclaration of local var {}", name),
				byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
			});
		}
		if errors.is_empty() {
			ctxt.locals.insert(name.elt, typ.elt);
			Ok(false)
		} else {
			Err(errors)
		}
	},
	Return(None) => {
		if expected_return_type.is_none() {
			Ok(true)
		} else {
			Err(vec![Error{
				err: "Cannot return void in a non-void function".to_owned(),
				byte_offset: s.byte_offset, approx_len: s.byte_len, file_id: s.file_id
			}])
		}
	},
	Return(Some(e)) => {
		//ctxt.type_for_lit_nulls = ctxt.type_for_lit_nulls;
		let (mut errors, result_ty) = match typecheck_expr(ctxt, funcs, e, typecache) {
			Err(errs) => (errs, None),
			Ok(()) => {
				debug_assert!(e.elt.typ.is_some());
				(Vec::new(), e.elt.typ)
			}
		};
		match expected_return_type {
			None => errors.push(Error{
				err: "Cannot return a value from a void function".to_owned(),
				byte_offset: s.byte_offset, approx_len: s.byte_len, file_id: s.file_id
			}),
			Some(t) => {
				if let Some(return_expr_type) = result_ty {
					if return_expr_type != t {
						errors.push(Error{
							err: format!("Cannot return a value of type {} in a function that returns {}", return_expr_type, t),
							byte_offset: e.byte_offset, approx_len: e.byte_len, file_id: e.file_id
						});
					}
				}
			}
		};
		if errors.is_empty() {
			Ok(true)
		} else {
			Err(errors)
		}
	},
	SCall(func_name, args) => {
		use FuncType::*;
		if PRINTF_FAMILY.contains(&func_name.elt){
			typecheck_printf(func_name.elt, args, ctxt, funcs, s.byte_offset, s.byte_len, s.file_id, typecache)?;
			return Ok(false);
		}
		let arg_type_list;
		match funcs.get(func_name.elt) {
			None => {
				return Err(vec![Error{
					err: format!("Could not find a function named '{}'", func_name),
					byte_offset: s.byte_offset, approx_len: s.byte_len, file_id: s.file_id
				}]);
			},
			Some(Generic{..}) => {
				return Err(vec![Error{
					err: format!("Function '{}' is generic", func_name),
					byte_offset: s.byte_offset, approx_len: s.byte_len, file_id: s.file_id
				}]);
			},
			Some(NonGeneric{args: arg_types, ..}) => {
				arg_type_list = arg_types;
			}
		};
		let mut errors = Vec::new();
		let mut check_against_expected_types = true;
		if args.len() != arg_type_list.len() {
			errors.push(Error{
				err: format!("Wrong number of args to {}: given {} args, should be {}", func_name.elt, args.len(), arg_type_list.len()),
				byte_offset: s.byte_offset, approx_len: s.byte_len, file_id: s.file_id
			});
			check_against_expected_types = false;
		}
		for (index, (arg_or_errors, correct_type)) in args.iter_mut()
				.zip(arg_type_list.iter())
				.map(|(arg, expected_type)| {
					ctxt.type_for_lit_nulls = Some(expected_type);
					let arg_or_errors = match typecheck_expr(ctxt, funcs, arg, typecache) {
						Err(err) => Err(err),
						Ok(()) => Ok(arg)
					};
					(arg_or_errors, expected_type)
				})
				.enumerate(){
			//not doing array-to-pointer decay like c, do &arr[0] instead
			match arg_or_errors {
				Err(mut errs) => errors.append(&mut errs),
				Ok(arg) => {
					if check_against_expected_types && arg.elt.typ.unwrap().ne(correct_type) {
						errors.push(Error{
							err: format!("Argument {} to {} has type {}, expected {}", index + 1, func_name.elt, arg.elt.typ.unwrap(), correct_type),
							byte_offset: arg.byte_offset, approx_len: arg.byte_len, file_id: arg.file_id
						})
					}
				}
			}
		}
		if errors.is_empty() {
			Ok(false)
		} else {
			Err(errors)
		}
	},
	GenericSCall{name: func_name, type_param, args} => {
		use FuncType::*;
		let mut errors = Vec::new();
		let mut type_param_was_valid = true;
		if let Err(err) = all_struct_names_valid(type_param, &ctxt.structs, &ctxt.type_var) {
			errors.push(err);
			type_param_was_valid = false;
		}
		let arg_type_list;
		let callee_mode;
		let type_var_string;
		match funcs.get(func_name.elt) {
			None => {
				errors.push(Error{
					err: format!("Could not find a function named '{}'", func_name.elt),
					byte_offset: func_name.byte_offset, approx_len: func_name.byte_len, file_id: func_name.file_id
				});
				return Err(errors);
			},
			Some(NonGeneric{..}) => {
				errors.push(Error{
					err: format!("Function '{}' is not generic", func_name),
					byte_offset: s.byte_offset, approx_len: s.byte_len, file_id: s.file_id
				});
				return Err(errors);
			},
			Some(Generic{mode, type_var: var_string, args: arg_types, ..}) => {
				arg_type_list = arg_types;
				callee_mode = mode;
				type_var_string = var_string;
			}
		};
		let mut check_against_expected_types = true;
		let type_var_str_in_type_var = type_param.recursively_find_type_var();
		match (type_var_str_in_type_var, &ctxt.type_var) {
			(None, _) => (),
			(Some(s), None) => {
				errors.push(Error{
					err: format!("Cannot use type variable '{} in non-generic function", s),
					byte_offset: type_param.byte_offset, approx_len: type_param.byte_len, file_id: type_param.file_id
				});
			},
			(Some(s), Some((current_func_type_var, current_func_mode))) => {
				if &s != current_func_type_var {
					errors.push(Error{
						err: format!("Type param passed to generic func {} contains unknown type variable '{}", func_name, s),
						byte_offset: type_param.byte_offset, approx_len: type_param.byte_len, file_id: type_param.file_id
					});
				}
				use PolymorphMode::*;
				if *callee_mode == Separated && *current_func_mode == Erased {
					errors.push(Error{
						err: format!("Cannot call separated function {} from erased function", func_name),
						byte_offset: func_name.byte_offset, approx_len: func_name.byte_len, file_id: func_name.file_id
					});
				}
			}
		};
		if args.len() != arg_type_list.len() {
			errors.push(Error{
				err: format!("Wrong number of args to {}: given {} args, should be {}", func_name.elt, args.len(), arg_type_list.len()),
				byte_offset: s.byte_offset, approx_len: s.byte_len, file_id: s.file_id
			});
			check_against_expected_types = false;
		}
		/*
		expr is:		name<type_var>(..args..)
		name has type:	return_type name<var_string>(..arg_type_list..)
		the monomorphed version of name would look like:
						return_type name_mangled_type_var(..arg_type_list with var_string replaced with type_var..)
		*/
		for (index, (arg_or_errors, correct_type)) in args.iter_mut()
				.zip(arg_type_list.iter())
				.map(|(arg, expected_type)| {
					//if the type param of this call was not valid, don't try to do any replacements
					//instead, just skip typechecking on any arg where a replacement would take place
					let correct_type = replace_type_var_with(expected_type, type_var_string, type_param.elt, typecache);
					if !type_param_was_valid && &correct_type != expected_type {
						return (Err(vec![]), correct_type);
					}
					ctxt.type_for_lit_nulls = Some(correct_type);
					let arg_or_errors = match typecheck_expr(ctxt, funcs, arg, typecache) {
						Err(err) => Err(err),
						Ok(()) => Ok(arg)
					};
					(arg_or_errors, correct_type)
				})
				.enumerate() {
			match arg_or_errors {
				Err(mut errs) => errors.append(&mut errs),
				Ok(arg) => {
					if check_against_expected_types && arg.elt.typ.unwrap().ne(correct_type) {
						errors.push(Error{
							err: format!("Argument {} to {} has type {}, expected {}", index + 1, func_name.elt, arg.elt.typ.unwrap(), correct_type),
							byte_offset: arg.byte_offset, approx_len: arg.byte_len, file_id: arg.file_id
						})
					}
				}
			}
		}
		if errors.is_empty() {
			Ok(false)
		} else {
			Err(errors)
		}
	},
	If(cond, then_block, else_block) => {
		ctxt.type_for_lit_nulls = Some(&Bool);
		let mut errors = Vec::new();
		if let Err(mut errs) = typecheck_expr(ctxt, funcs, cond, typecache) {
			errors.append(&mut errs);
		} else {
			let cond_ty = cond.elt.typ.unwrap();
			if cond_ty != &Bool {
				errors.push(Error{
					err: format!("condition of if statement must have type bool, not {}", cond_ty),
					byte_offset: cond.byte_offset, approx_len: cond.byte_len, file_id: cond.file_id
				});
			}
		}
		let then_result = typecheck_block(ctxt, funcs, then_block, expected_return_type, typecache);
		let else_result = typecheck_block(ctxt, funcs, else_block, expected_return_type, typecache);
		let mut both_return = false;
		if let (Ok(then_returns), Ok(else_returns)) = (&then_result, &else_result) {
			both_return = *then_returns && *else_returns;
		}
		if let Err(mut errs) = then_result {
			errors.append(&mut errs);
		}
		if let Err(mut errs) = else_result {
			errors.append(&mut errs);
		}
		if errors.is_empty() {
			Ok(both_return)
		} else {
			Err(errors)
		}
	},
	While(cond, body) => {
		ctxt.type_for_lit_nulls = Some(&Bool);
		let mut errors = Vec::new();
		if let Err(mut errs) = typecheck_expr(ctxt, funcs, cond, typecache) {
			errors.append(&mut errs);
		} else {
			let cond_ty = cond.elt.typ.unwrap();
			if cond_ty != &Bool {
				errors.push(Error{
					err: format!("condition of while must have type bool, not {}", cond_ty),
					byte_offset: cond.byte_offset, approx_len: cond.byte_len, file_id: cond.file_id
				});
			}
		}
		if let Err(mut errs) = typecheck_block(ctxt, funcs, body, expected_return_type, typecache) {
			errors.append(&mut errs);
		}
		if errors.is_empty() {
			Ok(false)
		} else {
			Err(errors)
		}
	}
}
}

pub fn typecheck_block<'src: 'arena, 'arena: 'body, 'body>(
		ctxt: &mut LocalTypeContext<'src, 'arena>,
		funcs: &FuncContext<'src, 'arena>,
		block: &'body mut Block<'src, 'arena>,
		expected_return_type: Option<&'arena Ty<'src, 'arena>>,
		typecache: &'arena TypeCache<'src, 'arena>)
		-> Result<bool, Vec<Error>> {
	let mut stmt_returns = false;
	let mut unreachable_err: Option<Error> = None;
	for stmt in block.0.iter_mut(){
		if stmt_returns && unreachable_err.is_none() {
			unreachable_err = Some(Error{
				err: "Unreachable statement".to_owned(),
				byte_offset: stmt.byte_offset, approx_len: stmt.byte_len, file_id: stmt.file_id
			});
		}
		stmt_returns |= typecheck_stmt(ctxt, funcs, stmt, expected_return_type, typecache)?;
	}
	if let Some(err) = unreachable_err {
		Err(vec![err])
	} else {
		Ok(stmt_returns)
	}
}

pub fn typecheck_func_decl<'src: 'arena, 'arena: 'body, 'body>(
		ctxt: &mut LocalTypeContext<'src, 'arena>,
		funcs: &FuncContext<'src, 'arena>,
		name: &Loc<&'src str>,
		args: &[(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)],
		body: &'body mut Block<'src, 'arena>,
		ret_type: Option<&'arena Ty<'src, 'arena>>,
		typecache: &'arena TypeCache<'src, 'arena>)
		 -> Result<(), Vec<Error>>{
	/*
	create a LocalTypeContext
	add all args to it as locals
	if ret_type is not None, make sure body definitely returns
	*/
	for (arg_ty, arg_name) in args.iter() {
		ctxt.locals.insert(arg_name.elt, arg_ty.elt);
	}
	//add errno to the LocalTypeContext as a local variable with type i32
	ctxt.locals.insert("errno", Ty::Int{signed: true, size: IntSize::Size32}.getref(typecache));
	let last_statement_definitely_returns = typecheck_block(ctxt, funcs, body, ret_type, typecache)?;
	if ret_type.is_some() && !last_statement_definitely_returns {
		return Err(vec![Error{
			err: format!("function '{}' might not return", name),
			byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
		}]);
	}
	Ok(())
}

fn traverse_struct_context<'src: 'arena, 'arena>(struct_context: &StructContext<'src, 'arena>, typecache: &'arena TypeCache<'src, 'arena>) -> Result<(), (String, &'src str, Option<&'src str>)> {
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
	type Node<'src, 'arena> = (&'src str, Option<&'arena Ty<'src, 'arena>>);
	const MAX_STRUCT_DEPTH: i32 = 100;
	let mut fully_explored_nodes: HashSet<Node> = HashSet::with_capacity(struct_context.len());
	let mut queue: VecDeque<Node> = VecDeque::with_capacity(struct_context.len());
	for (name, struct_type) in struct_context.iter(){
		let node = match struct_type {
			NonGeneric(_) => (*name, None),
			Generic{type_var, ..} => {
				let new_ty = Ty::TypeVar(type_var).getref(typecache);
				(*name, Some(new_ty))
			}
		};
		if fully_explored_nodes.contains(&node) { continue }
		queue.push_back(node);
		let mut seen_nodes: HashSet<Node> = HashSet::with_capacity(struct_context.len());
		let mut iterations = 0;
		while !queue.is_empty() {
			iterations += 1;
			if iterations >= MAX_STRUCT_DEPTH {
				return Err((format!("maximum struct depth ({}) reached when processing struct '{}'", MAX_STRUCT_DEPTH, name), name, None));
			}
			let current_node = queue.pop_front().unwrap();
			if fully_explored_nodes.contains(&current_node) {
				continue
			}
			if seen_nodes.contains(&current_node) {
				return Err((format!("struct '{}' is recursive", current_node.0), current_node.0, None));
			}
			seen_nodes.insert(current_node);
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
				for (field_name, field_type) in fields.iter(){
					if field_type.recursively_find_type_var().is_some() {
						return Err((format!("non-generic struct {} has a field of type {}", current_node.0, field_type), current_node.0, Some(field_name)));
					}
					use Ty::*;
					match field_type {
						Struct(s) => queue.push_back((s, None)),
						GenericStruct{type_param: fully_concrete_type, name} => queue.push_back((name, Some(fully_concrete_type))),
						_ => ()
					}
				}
			},
			//current node is a generic struct
			Some(type_param) => {
				//If the type_param is a concrete type, then I need to treat any instances of
				//the current struct's type param string as this type
				//to get the type param string, need to look up current_node.0 in struct_context

				let (current_mode, type_param_string_of_current_struct): (PolymorphMode, &str) = match struct_context.get(current_node.0).expect("why is the current struct's name not in the context?") {
					NonGeneric{..} => panic!("why is struct {} generic and non-generic?", current_node.0),
					Generic{type_var, mode, ..} => (*mode, type_var)
				};
				//the current type param can be concrete even if it is just a TypeVar.
				//It could be a different TypeVar
				let type_param_is_concrete: bool = type_param != &Ty::TypeVar(type_param_string_of_current_struct);
				for (field_name, field_type) in fields.iter(){
					use Ty::*;
					match (type_param_is_concrete, field_type.recursively_find_type_var()) {
						//make sure a struct with a TypeVar type param does not have any fields with other TypeVars
						(false, Some(field_param_str)) => {
							if type_param_string_of_current_struct != field_param_str {
								return Err((format!("struct {}@<'{}> has a field with an unknown type param, {}", current_node.0, type_param_string_of_current_struct, field_type), current_node.0, Some(field_name)));
							}
						},
						//make sure a struct a concrete type param does not have any fields with a TypeVar that is not the current struct's type var
						(true, Some(typevar)) if typevar != type_param_string_of_current_struct => {
							return Err((format!("struct {}@<{}> has a field with an unknown type param, {}", current_node.0, type_param, field_type), current_node.0, Some(field_name)));
						}
						_ => ()
					};
					//any TypeVars encountered henceforth are guaranteed to be valid,
					//but I will debug_assert them anyway
					match field_type {
						Struct(s) => queue.push_back((s, None)),
						GenericStruct{type_param, name} => {
							//if the current struct is erased, and the field struct is separated, and
							//the current struct is passing its TypeVar to it (type param is not concrete),
							//then there is an error
							let field_mode = match struct_context.get(name).expect("field does not exist") {
								NonGeneric{..} => panic!("why is struct {} generic and non-generic?", name),
								Generic{mode, ..} => mode
							};
							use PolymorphMode::*;
							let type_param_found_in_type_var = type_param.recursively_find_type_var();
							let field_type_param_is_concrete = type_param_found_in_type_var.is_none();
							if current_mode == Erased
								&& *field_mode == Separated
								&& !field_type_param_is_concrete {
								return Err((format!("struct {} passes an erased type var ('{}) to separated struct {}", current_node.0, type_param_string_of_current_struct, name), current_node.0, Some(field_name)));
							}
							let substituted1 = replace_type_var_with(type_param, type_param_string_of_current_struct, type_param, typecache);
							let type_param_string_of_field_struct: &str = match struct_context.get(name).unwrap_or_else(|| panic!("why is struct {} not in the context?", name)) {
								NonGeneric{..} => panic!("why is field struct {} generic and non-generic?", name),
								Generic{type_var, ..} => type_var
							};
							let temptyp = TypeVar(type_param_string_of_field_struct).getref(typecache);
							let substituted2 = replace_type_var_with(substituted1, type_param_string_of_current_struct, temptyp, typecache);
							queue.push_back((name, Some(substituted2)));

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
fn type_is_c_compatible<'src: 'arena, 'arena>(t: &'arena Ty<'src, 'arena>, structs: &StructContext<'src, 'arena>) -> bool {
use Ty::*;
match t {
	Ptr(Some(inner)) => type_is_c_compatible(inner, structs),
	Array{typ, ..} => type_is_c_compatible(typ, structs),
	Struct(s) => { match structs.get(s).unwrap() {
		StructType::Generic{..} => panic!("struct {} is a generic struct in the context, should have been caught by now by calling all_struct_names_valid", s),
		StructType::NonGeneric(fields) => fields.iter().all(|(_, field_ty)| type_is_c_compatible(field_ty, structs))
	}},
	TypeVar(_) | GenericStruct{..} => false,
	_ => true
}}

pub struct ProgramContext<'src: 'arena, 'arena> {
	pub structs: StructContext<'src, 'arena>,
	pub funcs: FuncContext<'src, 'arena>,
	pub globals: GlobalContext<'src, 'arena>
}

fn struct_err_with_loc<'src: 'arena, 'arena>(prog: &Program<'src, 'arena>, err_msg: String, struct_name: &'src str, field_name: Option<&'src str>) -> Error {
	for (name, fields) in prog.structs.iter()
		.map(|s| (s.name, s.fields))
		.chain(
			prog.erased_structs.iter().chain(prog.separated_structs.iter())
			.map(|s| (s.name, s.fields))
		) {
		if name.elt == struct_name {
			if let Some(field_name) = field_name {
				for (field_type_loc, field_name_loc) in fields.iter() {
					if field_name_loc.elt == field_name {
						return Error {
							err: err_msg, byte_offset: field_type_loc.byte_offset,
							approx_len: field_type_loc.byte_len, file_id: field_type_loc.file_id
						}
					}
				}
				panic!("field {} not found in struct {}", field_name, struct_name);
			} else {
				return Error{
					err: err_msg,
					byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
				};
			}
		}
	}
	panic!("struct {} not found in gdecls", struct_name);
}

pub fn typecheck_program<'src: 'arena, 'arena: 'prog, 'prog>(
	prog: &'prog mut Program<'src, 'arena>,
	typecache: &'arena TypeCache<'src, 'arena>,
	arena: &'arena bumpalo_herd::Member<'arena>)
	-> Result<ProgramContext<'src, 'arena>, Vec<Error>>{
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
	let mut errors = Vec::new();
	for Struct{name, fields} in prog.structs.iter() {
		if struct_context.contains_key(name.elt){
			errors.push(Error{
				err: format!("struct '{}' is declared more than once", name),
				byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
			});
		} else {
			let iter = fields.iter().map(|(t, n)| {(n.elt, t.elt)});
			let allocated_slice = &*arena.alloc_slice_fill_iter(iter);
			struct_context.insert(name.elt, StructType::NonGeneric(allocated_slice));
		}
	}
	for (mode, GenericStruct{name, var, fields}) in prog.erased_structs.iter()
			.map(|s| (PolymorphMode::Erased, s))
			.chain(prog.separated_structs.iter().map(|s| (PolymorphMode::Separated, s))) {
		if struct_context.contains_key(name.elt){
			errors.push(Error{
				err: format!("struct '{}' is declared more than once", name),
				byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
			});
		} else {
			let iter = fields.iter().map(|(t, n)| (n.elt, t.elt));
			let allocated_slice = &*arena.alloc_slice_fill_iter(iter);
			struct_context.insert(name, StructType::Generic{
				mode,
				type_var: var,
				fields: allocated_slice
			});
		}
	}
	//struct_context has been populated, now need to check for duplicate and invalid fields
	//don't iterate through struct_context, iterate through gdecls again to get location info
	for Struct{name, fields} in prog.structs.iter() {
		let mut seen_fields: HashSet<&str> = HashSet::new();
		for (field_type, field_name) in fields.iter() {
			if seen_fields.contains(field_name.elt) {
				errors.push(Error{
					err: format!("struct {} contains two fields named {}", name.elt, field_name.elt),
					byte_offset: field_name.byte_offset, approx_len: field_name.byte_len, file_id: field_name.file_id
				});
			}
			if let Err(err) = all_struct_names_valid(field_type, &struct_context, &None) {
				errors.push(err);
			}
			seen_fields.insert(field_name.elt);
		}
	}
	for (mode, GenericStruct{name, var, fields}) in prog.erased_structs.iter()
			.map(|s| (PolymorphMode::Erased, s))
			.chain(prog.separated_structs.iter().map(|s| (PolymorphMode::Separated, s))) {
		let mut seen_fields: HashSet<&str> = HashSet::new();
		for (field_type, field_name) in fields.iter() {
			if seen_fields.contains(field_name.elt) {
				errors.push(Error{
					err: format!("struct {} contains two fields named {}", name.elt, field_name.elt),
					byte_offset: field_name.byte_offset, approx_len: field_name.byte_len, file_id: field_name.file_id
				});
			}
			if let Err(err) = all_struct_names_valid(field_type, &struct_context, &Some((var, mode))) {
				errors.push(err);
			}
			seen_fields.insert(field_name.elt);
		}
	}
	//if there were non-existant structs/bad fields, can't really typecheck the rest
	if !errors.is_empty() {
		return Err(errors);
	}
	if let Err((msg, problematic_struct_name, problematic_field_opt)) = traverse_struct_context(&struct_context, typecache) {
		errors.push(struct_err_with_loc(&*prog, msg, problematic_struct_name, problematic_field_opt));
	}

	let mut func_context: FuncContext = HashMap::new();
	let mut global_context: GlobalContext = HashMap::new();

	//first, check all external decls for c compatibility, and add them to the func_context
	for ExternalFunc{ret_type, name, arg_types} in prog.external_funcs.iter() {
		match func_context.get(name.elt) {
			Some(FuncType::NonGeneric{return_type, args}) => {
				//extern declarations are allowed to be repeated if they have the same type
				if return_type != &ret_type.elt {
					use std::fmt::Write;
					let mut msg = format!("Two extern function declarations of {} do not have the same return type (Previously declared with return type ", name.elt);
					if let Some(t) = *return_type {
						write!(&mut msg, "{}", t).unwrap();
					} else {
						msg.push_str("void");
					}
					msg.push_str(", declared again with return type ");
					if let Some(t) = ret_type.elt {
						write!(&mut msg, "{}", t).unwrap();
					} else {
						msg.push_str("void");
					}
					msg.push(')');
					errors.push(Error{
						err: msg, byte_offset: ret_type.byte_offset,
						approx_len: ret_type.byte_len, file_id: ret_type.file_id
					})
				}
				if args.len() != arg_types.len() {
					errors.push(Error{
						err: format!("Two extern function declarations of {} do not have the same number of arguments (Previously declared with {} args, declared again with {} args)", name.elt, args.len(), arg_types.len()),
						byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
					});
				}
				for (i, (expected_ty, arg_ty_loc)) in args.iter().zip(arg_types.iter()).enumerate() {
					if expected_ty != &arg_ty_loc.elt {
						errors.push(Error{
							err: format!("Two extern function declarations of {} do not have the same type for argument {} (Previously declared with argument type {}, declared again with aragument type {})", name.elt, i+1, expected_ty, arg_ty_loc.elt),
							byte_offset: arg_ty_loc.byte_offset, approx_len: arg_ty_loc.byte_len, file_id: arg_ty_loc.file_id
						});
						//only report one error for mismatched types in redeclaration of extern
						break
					}
				}
				//if it is already in the func context with the same types, no need to check those types
				continue
			},
			Some(FuncType::Generic{..}) => panic!("extern function {} already in func context as generic", name),
			None => {
				//first time seeing this extern, check all arg types and return type
				let mut bad_extern = false;
				for (i, arg_type) in arg_types.iter().enumerate() {
					if let Err(err) = all_struct_names_valid(arg_type, &struct_context, &None) {
						bad_extern = true;
						errors.push(err);
					} else if !type_is_c_compatible(arg_type, &struct_context) {
						bad_extern = true;
						errors.push(Error{
							err: format!("argument {} to extern function {} has type {}, which is not C-compatible", i+1, name.elt, arg_type.elt),
							byte_offset: arg_type.byte_offset, approx_len: arg_type.byte_len, file_id: arg_type.file_id
						});
					}
				}
				if let Some(ret) = ret_type.elt {
					let ret_type_loc: Loc<&Ty<'src, 'arena>> = Loc{
						elt: ret, byte_offset: ret_type.byte_offset, byte_len: ret_type.byte_len, file_id: ret_type.file_id
					};
					if let Err(err) = all_struct_names_valid(&ret_type_loc, &struct_context, &None) {
						bad_extern = true;
						errors.push(err);
					} else if !type_is_c_compatible(ret, &struct_context) {
						bad_extern = true;
						errors.push(Error{
							err: format!("extern function {} has return type {}, which is not C-compatible", name.elt, ret),
							byte_offset: ret_type.byte_offset, approx_len: ret_type.byte_len, file_id: ret_type.file_id
						});
					}
				}
				if !bad_extern {
					let arg_types_iter = arg_types.iter().map(|t_loc| t_loc.elt);
					let allocated_slice = arena.alloc_slice_fill_iter(arg_types_iter);
					func_context.insert(name.elt, FuncType::NonGeneric{
						return_type: ret_type.elt,
						args: allocated_slice
					});
				}
			},
		};
	}
	for Func{ret_type, name: func_name, args, ..} in prog.funcs.iter() {
		if func_context.contains_key(func_name.elt) {
			errors.push(Error{
				err: format!("Function '{}' is declared more than once", func_name),
				byte_offset: func_name.byte_offset, approx_len: func_name.byte_len, file_id: func_name.file_id
			});
			continue
		}
		if global_context.contains_key(func_name.elt) {
			errors.push(Error{
				err: format!("Cannot declare a function named '{}', a global cariable of that name already exists", func_name.elt),
				byte_offset: func_name.byte_offset, approx_len: func_name.byte_len, file_id: func_name.file_id
			});
			continue
		}
		if let Some(ret) = ret_type.elt {
			let ret_type_loc: Loc<&Ty<'src, 'arena>> = Loc{
				elt: ret, byte_offset: ret_type.byte_offset, byte_len: ret_type.byte_len, file_id: ret_type.file_id
			};
			if let Err(err) = all_struct_names_valid(&ret_type_loc, &struct_context, &None) {
				errors.push(err);
				continue
			} else if let Some(s) = ret.recursively_find_type_var() {
				errors.push(Error{
					err: format!("Return type of non-generic function {} contains type variable '{}", func_name.elt, s),
					byte_offset: ret_type.byte_offset, approx_len: ret_type.byte_len, file_id: ret_type.file_id
				});
				continue
			}
		}
		let mut names: HashSet<&'src str> = HashSet::new();
		for (arg_type, arg_name) in args.iter(){
			if names.contains(arg_name.elt){
				errors.push(Error{
					err: format!("Function '{}' contains two arguments both named '{}'", func_name, arg_name),
					byte_offset: arg_name.byte_offset, approx_len: arg_name.byte_len, file_id: arg_name.file_id
				});
			} else {
				names.insert(arg_name.elt);
			}
			if let Err(e) = all_struct_names_valid(arg_type, &struct_context, &None) {
				errors.push(e);
			}
			if let Some(s) = arg_type.recursively_find_type_var() {
				errors.push(Error{
					err: format!("found type variable '{} in type signature of non-generic function {}", s, func_name),
					byte_offset: arg_type.byte_offset, approx_len: arg_type.byte_len, file_id: arg_type.file_id
				});
			}
		}
		let arg_types_iter = args.iter().map(|(t,_)| t.elt);
		let allocated_slice = arena.alloc_slice_fill_iter(arg_types_iter);
		func_context.insert(func_name.elt, FuncType::NonGeneric{
			return_type: ret_type.elt,
			args: allocated_slice
		});
	}
	for (mode, GenericFunc{name: func_name, ret_type, args, var, ..}) in prog.erased_funcs.iter()
			.map(|f| (PolymorphMode::Erased, f))
			.chain(prog.separated_funcs.iter().map(|f| (PolymorphMode::Separated, f))) {
		if func_context.contains_key(func_name.elt) {
			errors.push(Error{
				err: format!("Function '{}' is declared more than once", func_name),
				byte_offset: func_name.byte_offset, approx_len: func_name.byte_len, file_id: func_name.file_id
			});
			continue
		}
		if global_context.contains_key(func_name.elt) {
			errors.push(Error{
				err: format!("Cannot declare a function named '{}', a global cariable of that name already exists", func_name.elt),
				byte_offset: func_name.byte_offset, approx_len: func_name.byte_len, file_id: func_name.file_id
			});
			continue
		}
		if let Some(ret) = ret_type.elt {
			let ret_type_loc: Loc<&Ty<'src, 'arena>> = Loc{
				elt: ret, byte_offset: ret_type.byte_offset, byte_len: ret_type.byte_len, file_id: ret_type.file_id
			};
			if let Err(e) = all_struct_names_valid(&ret_type_loc, &struct_context, &Some((var, mode))) {
				errors.push(e);
				continue
			} else {
				match ret.recursively_find_type_var() {
					Some(s) if s != var.elt => {
						errors.push(Error{
							err: format!("Found unknown type variable '{} in return type of function {}", s, func_name),
							byte_offset: ret_type.byte_offset, approx_len: ret_type.byte_len, file_id: ret_type.file_id
						});
						continue
					}
					_ => ()
				};
			}
		}
		let mut names: HashSet<&'src str> = HashSet::new();
		for (arg_type, arg_name) in args.iter(){
			if names.contains(arg_name.elt){
				errors.push(Error{
					err: format!("Function '{}' contains two arguments both named '{}'", func_name, arg_name),
					byte_offset: arg_name.byte_offset, approx_len: arg_name.byte_len, file_id: arg_name.file_id
				});
			} else {
				names.insert(arg_name.elt);
			}
			if let Err(e) = all_struct_names_valid(arg_type, &struct_context, &Some((var, mode))) {
				errors.push(e);
			}
			match arg_type.elt.recursively_find_type_var() {
				Some(s) if s != var.elt => {
					errors.push(Error{
						err: format!("Found unknown type variable '{} in type signature of function {}", s, func_name),
						byte_offset: arg_type.byte_offset, approx_len: arg_type.byte_len, file_id: arg_type.file_id
					});
				}
				_ => ()
			}
		}
		let arg_types_iter = args.iter().map(|(t, _)| t.elt);
		let allocated_slice = arena.alloc_slice_fill_iter(arg_types_iter);
		func_context.insert(func_name, FuncType::Generic {
			return_type: ret_type.elt,
			args: allocated_slice,
			mode,
			type_var: var,
		});
	}
	for (t, name) in prog.global_vars.iter() {
		if let Err(e) = all_struct_names_valid(t, &struct_context, &None) {
			errors.push(e);
		}
		if let Some(s) = t.elt.recursively_find_type_var() {
			errors.push(Error{
				err: format!("Found type variable '{} in type of global variable", s),
				byte_offset: t.byte_offset, approx_len: t.byte_len, file_id: t.file_id
			});
		}
		if global_context.contains_key(name.elt) {
			errors.push(Error{
				err: format!("Cannot have two global variables both named '{}'", name),
				byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
			});
		}
		if func_context.contains_key(name.elt) {
			errors.push(Error{
				err: format!("cannot declare global variable '{}', a function is already declared with that name", name),
				byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
			});
		}
		//a global var needs to have a known size at compile time, so it cannot be an erased struct,
		//or any array of erased structs, or a struct that contains an erased struct
		if t.elt.is_DST(&struct_context, None, typecache) {
			errors.push(Error{
				err: format!("global variable {} does not have a statically known size because it contains an erased struct", name),
				byte_offset: t.byte_offset, approx_len: t.byte_len, file_id: t.file_id
			});
		}
		global_context.insert(name, t);
	}
	if !errors.is_empty() {
		return Err(errors);
	}
	for Func{ret_type, name, args, body} in prog.funcs.iter_mut() {
		let (mut ctxt, _) = get_empty_localtypecontext();
		//kind of weird, but in order to keep the LocalTypeContext the same and avoid
		//cloning the struct_context all the time, I need to move it into this temporary
		//ctxt variable, then move it back out (same for global_context)
		ctxt.globals = global_context;
		ctxt.structs = struct_context;
		if let Err(mut errs) = typecheck_func_decl(&mut ctxt, &func_context, name, args, body, ret_type.elt, typecache) {
			errors.append(&mut errs);
		}
		struct_context = ctxt.structs;
		global_context = ctxt.globals;
	}
	for (mode, GenericFunc{name: func_name, ret_type, args, var, body}) in prog.erased_funcs.iter_mut()
			.map(|f| (PolymorphMode::Erased, f))
			.chain(prog.separated_funcs.iter_mut().map(|f| (PolymorphMode::Separated, f))) {
		let (mut ctxt, _) = get_empty_localtypecontext();
		ctxt.type_var = Some((var.elt, mode));		
		ctxt.globals = global_context;
		ctxt.structs = struct_context;
		if let Err(mut errs) = typecheck_func_decl(&mut ctxt, &func_context, func_name, args, body, ret_type.elt, typecache) {
			errors.append(&mut errs);
		}
		struct_context = ctxt.structs;
		global_context = ctxt.globals;
	}

	fn err_with_main_loc<'src: 'arena, 'arena, Iter>(msg: String, names: Iter) -> Error
		where Iter: Iterator<Item = Loc<&'src str>> {
		for name in names {
			if name.elt == "main" {
				return Error{
					err: msg, byte_offset: name.byte_offset, approx_len: name.byte_len, file_id: name.file_id
				}
			}
		}
		panic!("no gdecl found with name main")
	}

	//make sure main has the right type signature
	let main_err_msg: Option<(String, Option<PolymorphMode>)> = match func_context.get("main") {
		Some(FuncType::Generic{mode, ..}) => {
			Some(("main() cannot be a generic function".to_owned(), Some(*mode)))
		},
		Some(FuncType::NonGeneric{return_type, args}) => {
			let return_type_is_correct = return_type == &Some(&Ty::Int{
				signed: true, size: IntSize::Size32
			});
			let args_are_correct_simple = args.is_empty();
			let args_are_correct_extended =
				args.len() == 2
				&& args[0] == &Ty::Int{signed: true, size: IntSize::Size32}
				&& args[1] == &Ty::Ptr(Some(&Ty::Ptr(Some(
					&Ty::Int{signed: false, size: IntSize::Size8}
				))))
			;
			let args_are_correct = args_are_correct_simple || args_are_correct_extended;
			if !return_type_is_correct || !args_are_correct {
				Some(("main() must have type i32 main() or i32 main(i32, u8**)".to_owned(), None))
			} else {
				None
			}
		},
		None => None
	};
	//only find main loc if there is a type error with main
	match main_err_msg {
		Some((msg, None)) => {
			errors.push(err_with_main_loc(msg, prog.funcs.iter().map(|f| f.name)));
		},
		Some((msg, Some(PolymorphMode::Erased))) => {
			errors.push(err_with_main_loc(msg, prog.erased_funcs.iter().map(|f| f.name)));
		},
		Some((msg, Some(PolymorphMode::Separated))) => {
			errors.push(err_with_main_loc(msg, prog.separated_funcs.iter().map(|f| f.name)));
		},
		None => ()
	};
	if errors.is_empty() {
		Ok(ProgramContext{
			structs: struct_context,
			funcs: func_context,
			globals: global_context
		})
	} else {
		Err(errors)
	}
}
