use crate::ast;
use crate::typechecker;
use crate::llvm;

fn cmp_ty(t: &ast::Ty, struct_context: &typechecker::StructContext) -> llvm::Ty {
	match t {
		ast::Ty::Bool => llvm::Ty::Bool,
		ast::Ty::Int{size: ast::IntSize::Size8, signed} => llvm::Ty::Int{bits: 8, signed: *signed},
		ast::Ty::Int{size: ast::IntSize::Size16, signed} => llvm::Ty::Int{bits: 16, signed: *signed},
		ast::Ty::Int{size: ast::IntSize::Size32, signed} => llvm::Ty::Int{bits: 32, signed: *signed},
		ast::Ty::Int{size: ast::IntSize::Size64, signed} => llvm::Ty::Int{bits: 64, signed: *signed},
		ast::Ty::Float(ast::FloatSize::FSize32) => llvm::Ty::Float32,
		ast::Ty::Float(ast::FloatSize::FSize64) => llvm::Ty::Float64,
		ast::Ty::Ptr(None) => llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
		ast::Ty::Ptr(Some(t1)) => llvm::Ty::Ptr(Box::new(cmp_ty(t1, struct_context))),
		ast::Ty::Array{length, typ} => llvm::Ty::Array{length: *length as usize, typ: Box::new(cmp_ty(typ, struct_context))},
		ast::Ty::Struct(s) => llvm::Ty::NamedStruct(s.clone()),
		ast::Ty::TypeVar(_) => panic!("cmp_ty of TypeVar not implemented yet"),
		ast::Ty::GenericStruct{..} => panic!("cmp_ty of GenericStruct not implemented yet"),
	}
}

#[allow(unused)]
static mut GENSYM_COUNT: usize = 0;
pub fn gensym(s: &str) -> String {
	let n_string;
	unsafe {
		GENSYM_COUNT += 1;
		n_string = GENSYM_COUNT.to_string();
	}
	let mut result_string = String::with_capacity(s.len() + n_string.len());
	result_string.push_str(s);
	result_string.push_str(&n_string);
	result_string
}

/*
actually figuring out the size of a type is not possible/difficult due to struct packing,
which llvm controls. instead, sizeof will be replaced with llvm instructions that compute the size
of the type. This is technically a runtime operation, but will almost certainly get optimized out.
https://stackoverflow.com/questions/14608250/how-can-i-find-the-size-of-a-type

this function is left here just in case I need it later
fn sizeof(t: &ast::Ty, struct_context: &typechecker::StructContext, instantiation: Option<&ast::Ty>) -> u64 {
	//instantiation (current idea):
	//in a separated function instantiation, this will be set to Some(concrete_type)
	//in an erased function, this will be set to None
	use ast::IntSize::*;
	use ast::FloatSize::*;
	use ast::Ty::*;
	use typechecker::StructType::*;
	match t {
		Bool | Int{size: Size8, ..} => 1,
		Int{size: Size16, ..} => 2,
		Int{size: Size32, ..} | Float(FSize32) => 4,
		Int{size: Size64, ..} | Float(FSize64) | Ptr(_) => 8,
		Array{length, typ} => sizeof(typ, struct_context, instantiation) * *length,
		Struct(name) => {
			let names_and_types= match struct_context.get(name) {
				None => panic!("struct {} is not in the struct_context", name),
				Some(Generic{..}) => panic!("struct {} is generic, expected non-generic struct", name),
				Some(NonGeneric(names_and_types)) => names_and_types
			};
			names_and_types.iter().map(|(_name, t)| sizeof(t, struct_context, instantiation)).sum()
		},
		//There should be only be one TypeVar in a function, so I can ignore the string here
		TypeVar(_) => {
			match instantiation {
				None => 8,
				Some(t) => sizeof(t, struct_context, instantiation)
			}
		},
		GenericStruct{type_var: type_param, name} => {
			match struct_context.get(name) {
				None => panic!("generic struct {} is not in the struct_context", name),
				Some(NonGeneric(_)) => panic!("struct {} is not generic, expected generic struct", name),
				Some(Generic{mode: _, type_var, fields: names_and_types}) => {
					//mode is unused here, is this ok?
					names_and_types.iter().map(|(_name, field_type)| {
						//replace type_var with type_param in all fields
						use crate::typechecker::replace_type_var_with;
						let cloned_field_type = field_type.clone();
						let replaced_field_type = replace_type_var_with(cloned_field_type, type_var, (type_param as &ast::Ty).clone());
						sizeof(&replaced_field_type, struct_context, instantiation)
					}).sum()
				}
			}
		}
	}
}
*/
