use crate::ast;
use crate::typechecker;
use crate::llvm;
use std::collections::HashMap;

type Context = HashMap<String, (llvm::Ty, llvm::Operand)>;

enum Component{
	Label(String),							//label of a block
	Instr(String, llvm::Instruction),		//regular instruction
	Term(llvm::Terminator),					//terminator of a block
	GlobalString(String, llvm::GlobalDecl),	//string that needs to be moved to global scope
	//Alloca'd memory is valid for the entire function, so moving them to the entry block is useless
		//unless I need the location of a variable before I Alloca it?
	//Entry(String, llvm::Instruction),		//instruction that needs to be moved to the entry block (usually an Alloca Instruction)
}

type Stream = Vec<Component>;

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

struct ExpResult{
	llvm_typ: llvm::Ty,
	llvm_op: llvm::Operand,
	stream: Stream,

	/*Not doing this currently, because I would have to store ast::Tys in the context as well
	//only include this field when running with debug assertions to verify llvm_typ == cmp(src_typ)
	#[cfg(debug_assertions)]
	src_typ: ast::Ty,
	*/
}

fn cmp_exp(e: &ast::Expr, ctxt: &Context, type_for_lit_nulls: &Option<llvm::Ty>, struct_context: &typechecker::StructContext) -> ExpResult { match e {
	ast::Expr::LitNull => match type_for_lit_nulls {
		None => panic!("type_for_lit_nulls is None in cmp_exp"),
		Some(t @ llvm::Ty::Ptr(_)) => {
			ExpResult{
				llvm_typ: t.clone(),
				llvm_op: llvm::Operand::Const(llvm::Constant::Null(t.clone())),
				stream: vec![],
			}
		},
		Some(t) => panic!("type_for_lit_nulls in cmp_exp is not a pointer: {:?}", t)
	},
	ast::Expr::LitBool(b) => ExpResult{
		llvm_typ: llvm::Ty::Bool,
		llvm_op: llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: if *b {1} else {0} }),
		stream: vec![],
	},
	ast::Expr::LitSignedInt(i) => ExpResult{
		llvm_typ: llvm::Ty::Int{bits: 64, signed: true},
		llvm_op: llvm::Operand::Const(llvm::Constant::SInt{bits: 64, val: *i}),
		stream: vec![],
	},
	ast::Expr::LitUnsignedInt(i) => ExpResult{
		llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
		llvm_op: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: *i}),
		stream: vec![],
	},
	ast::Expr::LitFloat(f) => ExpResult{
		llvm_typ: llvm::Ty::Float64,
		llvm_op: llvm::Operand::Const(llvm::Constant::Float64(*f)),
		stream: vec![],
	},
	ast::Expr::LitString(s) => {
		let global_string_ident = gensym("string_literal_array");
		let casted_local_ident = gensym("string_pointer");
		let global_typ = llvm::Ty::Array{
			length: s.len()+1,
			typ: Box::new(llvm::Ty::Int{bits: 8, signed: false})
		};
		let stream = vec![
			Component::GlobalString(global_string_ident.clone(), llvm::GlobalDecl{
				typ: global_typ.clone(),
				init: llvm::GlobalInit::GString(s.clone())
			}),
			Component::Instr(casted_local_ident.clone(), llvm::Instruction::Bitcast{
				original_typ: llvm::Ty::Ptr(Box::new(global_typ)),
				new_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
				op: llvm::Operand::Global(global_string_ident.clone())
			})
		];
		ExpResult{
			llvm_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
			llvm_op: llvm::Operand::Local(casted_local_ident),
			stream,
		}
	},
	ast::Expr::Id(s) => cmp_lvalue_to_rvalue(e, &format!("{}_loaded", s) as &str, ctxt, struct_context),
	ast::Expr::Index(_,_) => cmp_lvalue_to_rvalue(e, "index_loaded", ctxt, struct_context),
	ast::Expr::Proj(_,_) => cmp_lvalue_to_rvalue(e, "proj_loaded", ctxt, struct_context),
	ast::Expr::Deref(_) => cmp_lvalue_to_rvalue(e, "deref_loaded", ctxt, struct_context),
	ast::Expr::LitArr(exprs) => {
		/*
		%init0 = cmp_exp exprs[0]
		...
		%initN = cmp_exp exprs[N]
		%arr_base = alloca [exprs.len() x type of exprs[0]]
		%arr_as_ptr = bitcast [exprs.len() x type of exprs[0]]* %arr_base to (type of exprs[0])*
		store [N x type of exprs[0]] [ty %init0, .. , ty %initN], [N x type of exprs[0]]* %arr_base
		%arr_as_ptr
		*/
		let mut stream: Stream = Vec::new();
		let llvm_type_of_first_expr;
		let mut expr_operands: Vec<llvm::Operand> = Vec::with_capacity(exprs.len());
		if exprs.len() == 0 {
			llvm_type_of_first_expr = llvm::Ty::Int{bits: 64, signed: true};
		} else {
			//ignoring the possibility of the first expr being a LitNull, not setting type_for_lit_nulls
			let mut init_0_result = cmp_exp(&exprs[0], ctxt, type_for_lit_nulls, struct_context);
			llvm_type_of_first_expr = init_0_result.llvm_typ;
			stream.append(&mut init_0_result.stream);
			expr_operands.push(init_0_result.llvm_op);
			let new_type_for_lit_nulls = Some(llvm_type_of_first_expr.clone());
			for init in exprs[1..].iter() {
				let mut result = cmp_exp(init, ctxt, &new_type_for_lit_nulls, struct_context);
				debug_assert_eq!(llvm_type_of_first_expr, result.llvm_typ);
				stream.append(&mut result.stream);
				expr_operands.push(result.llvm_op);
			}
		}
		let llvm_array_type = llvm::Ty::Array{length: exprs.len(), typ: Box::new(llvm_type_of_first_expr.clone())};
		let llvm_ptr_type = llvm::Ty::Ptr(Box::new(llvm_type_of_first_expr.clone()));
		let arr_base = gensym("arr_base");
		let arr_as_ptr = gensym("arr_as_ptr");
		stream.push(Component::Instr(arr_base.clone(), llvm::Instruction::Alloca(llvm_array_type.clone())));
		stream.push(Component::Instr(arr_as_ptr.clone(), llvm::Instruction::Bitcast{
			original_typ: llvm::Ty::Ptr(Box::new(llvm_array_type.clone())),
			new_typ: llvm_ptr_type.clone(),
			op: llvm::Operand::Local(arr_base.clone())
		}));
		stream.push(Component::Instr(String::new(), llvm::Instruction::Store{
			typ: llvm_array_type,
			data: llvm::Operand::Array{typ: llvm_type_of_first_expr, elements: expr_operands},
			dest: llvm::Operand::Local(arr_base)
		}));
		ExpResult{
			llvm_typ: llvm_ptr_type,
			llvm_op: llvm::Operand::Local(arr_as_ptr),
			stream
		}
	},
	_ => todo!()
}}

//the op this function returns is a pointer to where the data is stored
//the llvm::Ty this function returns is the type of the thing being pointed to, it may not be a Ptr
fn cmp_lvalue(e: &ast::Expr, ctxt: &Context, struct_context: &typechecker::StructContext) -> ExpResult { match e {
	ast::Expr::Id(s) => {
		let (ll_ty, ll_op) = ctxt.get(s).unwrap_or_else(|| panic!("why is variable {} not in the context?", s));
		ExpResult{
			llvm_typ: ll_ty.clone(),
			llvm_op: ll_op.clone(),
			stream: vec![]
		}
	},
	ast::Expr::Index(base, index) => {
		/*
		%index = cmp_exp(index)
		%base_ptr = cmp_exp(base)
		%result = getelementptr *base_typ, base_typ %base_ptr, %index
		*/
		let base_result = cmp_exp(base as &ast::Expr, ctxt, &None, struct_context);
		let mut index_result = cmp_exp(index as &ast::Expr, ctxt, &None, struct_context);
		let result_op = gensym("subscript");
		let result_typ;
		if let llvm::Ty::Ptr(t) = base_result.llvm_typ.clone() {
			result_typ = *t;
		} else {
			panic!("index base llvm type is not a Ptr");
		}
		let mut stream = base_result.stream;
		stream.append(&mut index_result.stream);
		stream.push(Component::Instr(result_op.clone(), llvm::Instruction::Gep{
			typ: result_typ.clone(),
			base: base_result.llvm_op,
			offsets: vec![index_result.llvm_op]
		}));
		ExpResult{
			llvm_typ: result_typ,
			llvm_op: llvm::Operand::Local(result_op),
			stream: stream
		}
	},
	ast::Expr::Proj(base, field_name) => {
		/*
		%base = cmp_lvalue(base)
		;if base points to a ptr
		%base_loaded = load base_typ*, base_typ** %base
		%field_ptr = getelementptr base_typ, base_typ* %base_loaded, i32 0, field_index(field_name, struct_context)
		*/
		let base_result = cmp_exp(base as &ast::Expr, ctxt, &None, struct_context);
		let mut stream = base_result.stream;
		let (base_is_ptr, struct_name) = match base_result.llvm_typ.clone() {
			llvm::Ty::NamedStruct(s) => (false, s),
			llvm::Ty::Ptr(boxed) => match *boxed {
				llvm::Ty::NamedStruct(s) => (true, s),
				t => panic!("Proj base has llvm type Ptr({:?})", t)
			}
			t => panic!("Proj base has llvm type {:?}", t)
		};
		let fields: &Vec<(String, ast::Ty)> = match struct_context.get(&struct_name) {
			None => panic!("struct {} not in struct_context", &struct_name),
			Some(typechecker::StructType::NonGeneric(fields)) => fields,
			Some(typechecker::StructType::Generic{fields, ..}) => {
				eprintln!("Warning: Projecting off of generic struct, generics not yet implemented");
				fields
			}
		};
		let mut field_index: Option<u32> = None;
		let mut result_ty: Option<llvm::Ty> = None;
		for (i, (name, src_ty)) in fields.iter().enumerate() {
			if name == field_name {
				use std::convert::TryFrom;
				field_index = Some(u32::try_from(i).unwrap_or_else(|_| panic!("error converting field index {} to u32", i) ));
				result_ty = Some(cmp_ty(src_ty, struct_context));
			}
		}
		let base_loaded_op: llvm::Operand;
		if base_is_ptr {
			let base_loaded_uid = gensym("base_loaded");
			base_loaded_op = llvm::Operand::Local(base_loaded_uid.clone());
			stream.push(Component::Instr(base_loaded_uid, llvm::Instruction::Load{
				typ: base_result.llvm_typ.clone(),
				src: base_result.llvm_op
			}));
		} else {
			base_loaded_op = base_result.llvm_op;
		}
		let field_index = field_index.unwrap_or_else(|| panic!("field name {} not found in struct {}", field_name, struct_name) );
		let result_ty = result_ty.unwrap();
		let field_ptr_uid = gensym("field_ptr");
		stream.push(Component::Instr(field_ptr_uid.clone(), llvm::Instruction::Gep{
			typ: base_result.llvm_typ,
			base: base_loaded_op,
			offsets: vec![
				llvm::Operand::Const(llvm::Constant::UInt{bits: 32, val: 0}),
				llvm::Operand::Const(llvm::Constant::UInt{bits: 32, val: field_index as u64})
			]
		}));
		ExpResult{
			llvm_typ: result_ty,
			llvm_op: llvm::Operand::Local(field_ptr_uid),
			stream: stream
		}
	},
	ast::Expr::Deref(base) => {
		let base = base as &ast::Expr;
		let base_result = cmp_exp(base, ctxt, &None, struct_context);
		base_result
	},
	other => panic!("{:?} is not a valid lvalue")
}}

fn cmp_lvalue_to_rvalue(e: &ast::Expr, gensym_seed: &str, ctxt: &Context, struct_context: &typechecker::StructContext) -> ExpResult {
	let mut lvalue_result = cmp_lvalue(e, ctxt, struct_context);
	let loaded_id = gensym(gensym_seed);
	let new_stream: Stream = vec![
		Component::Instr(loaded_id.clone(), llvm::Instruction::Load{
			typ: llvm::Ty::Ptr(Box::new(lvalue_result.llvm_typ.clone())),
			src: lvalue_result.llvm_op
		})
	];
	lvalue_result.stream = new_stream;
	//don't need to change the typ, it is already the type of the var
	lvalue_result.llvm_op = llvm::Operand::Local(loaded_id);
	lvalue_result
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
