use crate::ast;
use crate::typechecker;

fn cmp_ty(t: &ast::Ty, struct_context: &typechecker::StructContext, types: &llvm_ir::types::Types) -> llvm_ir::types::TypeRef {
	use ast::Ty::*;
	match t {
		Bool => types.bool(),
		Int{size: ast::IntSize::Size8, ..} => types.i8(),
		Int{size: ast::IntSize::Size16, ..} => types.i16(),
		Int{size: ast::IntSize::Size32, ..} => types.i32(),
		Int{size: ast::IntSize::Size64, ..} => types.i64(),
		Float(ast::FloatSize::FSize32) => types.single(),
		Float(ast::FloatSize::FSize64) => types.double(),
		Ptr(None) => types.pointer_to(types.i8()),
		Ptr(Some(t1)) => types.pointer_to(cmp_ty(t1 as &ast::Ty, struct_context, types)),
		Array{length, typ} => types.array_of(cmp_ty(typ, struct_context, types), *length as usize),
		Struct(s) => types.named_struct(s).unwrap_or_else(|| panic!("struct {} not found in types", s)),
		TypeVar(_) => panic!("cmp_ty of TypeVar not implemented yet"),
		GenericStruct{..} => panic!("cmp_ty of GenericStruct not implemented yet"),
	}
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
