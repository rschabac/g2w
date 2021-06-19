use crate::ast;
use crate::typechecker;
use crate::llvm;
use std::collections::{HashSet, HashMap, VecDeque};

//TODO: too many contexts! make an AllContext, might need multiple lifetime parameters
pub struct Context<'a>{
	locals: HashMap<String, (llvm::Ty, llvm::Operand)>,
	globals: &'a HashMap<String, (llvm::Ty, llvm::Operand)>,
	funcs: &'a typechecker::FuncContext,
	structs: &'a typechecker::StructContext,
	mode: Option<ast::PolymorphMode>,
}
impl<'a> Context<'a> {
	fn get_var(&self, name: &str) -> &(llvm::Ty, llvm::Operand) {
		self.locals.get(name)
			.or_else(|| self.globals.get(name))
			.unwrap_or_else(|| panic!("why is variable {} not in the context", name))
	}
}

#[allow(clippy::large_enum_variant)]
pub enum Component{
	Label(String),							//label of a block
	Instr(String, llvm::Instruction),		//regular instruction
	Term(llvm::Terminator),					//terminator of a block
	GlobalString(String, llvm::GlobalDecl),	//string that needs to be moved to global scope
	//Alloca'd memory is valid for the entire function, so moving them to the entry block is useless
		//unless I need the location of a variable before I Alloca it?
	//Entry(String, llvm::Instruction),		//instruction that needs to be moved to the entry block (usually an Alloca Instruction)
}

pub type Stream = Vec<Component>;

//If I want to parallelize compilation, each thread will need its own gensym
static mut GENSYM_COUNT: usize = 0;
pub fn gensym(s: &str) -> String {
	let n_copy;
	unsafe {
		GENSYM_COUNT += 1;
		n_copy = GENSYM_COUNT;
	}
	let n_string = n_copy.to_string();
	let mut result_string = String::with_capacity(s.len() + n_string.len() + 1);
	result_string.push('_');
	result_string.push_str(s);
	result_string.push_str(&n_string);
	result_string
}

/*
to cmp struct A@<bool>, this function needs to know if A is separated or not (needs a typechecker::StructContext)
if cmp_ty(struct A@<'f>) is called from a generic function,
	cmp_{exp,stmt,...} is responsible for knowing the right type for 'f
	(either void* if it is an erased function, or its type param if it is separated)
*/
fn cmp_ty(t: &ast::Ty, structs: &typechecker::StructContext, type_var_replacement: llvm::Ty) -> llvm::Ty {
	if t.is_DST(structs) {
		return llvm::Ty::Dynamic(t.clone());
	}
	match t {
		ast::Ty::Bool => llvm::Ty::Int{bits: 1, signed: false},
		ast::Ty::Int{size: ast::IntSize::Size8, signed} => llvm::Ty::Int{bits: 8, signed: *signed},
		ast::Ty::Int{size: ast::IntSize::Size16, signed} => llvm::Ty::Int{bits: 16, signed: *signed},
		ast::Ty::Int{size: ast::IntSize::Size32, signed} => llvm::Ty::Int{bits: 32, signed: *signed},
		ast::Ty::Int{size: ast::IntSize::Size64, signed} => llvm::Ty::Int{bits: 64, signed: *signed},
		ast::Ty::Float(ast::FloatSize::FSize32) => llvm::Ty::Float32,
		ast::Ty::Float(ast::FloatSize::FSize64) => llvm::Ty::Float64,
		ast::Ty::Ptr(None) => llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
		ast::Ty::Ptr(Some(t1)) => llvm::Ty::Ptr(Box::new(cmp_ty(t1, structs, type_var_replacement))),
		ast::Ty::Array{length, typ} => llvm::Ty::Array{length: *length as usize, typ: Box::new(cmp_ty(typ, structs, type_var_replacement))},
		ast::Ty::Struct(s) => llvm::Ty::NamedStruct(s.clone()),
		ast::Ty::GenericStruct{type_var: type_param, name} => {
			debug_assert!(type_param.recursively_find_type_var().is_none(), "cmp_ty called on generic struct with a type param that is not completely concrete, {:?}", t);
			match structs.get(name) {
				Some(typechecker::StructType::Generic{mode: ast::PolymorphMode::Erased, ..}) =>
					//already checked for is_DST above
					unreachable!(),
				Some(typechecker::StructType::Generic{mode: ast::PolymorphMode::Separated, ..}) => {
					llvm::Ty::NamedStruct(mangle(name, type_param))
				}
				None => panic!("could not find {} in struct context", name),
				Some(typechecker::StructType::NonGeneric(_)) => panic!("struct {} is not generic", name),
			}
		},
		ast::Ty::TypeVar(s) => {
			debug_assert!(s != "_should_not_happen", "TypeVar is _should_not_happen");
			debug_assert!(type_var_replacement != llvm::Ty::Void, "cannot replace type var with llvm::void");
			type_var_replacement
		}
	}
}

pub struct ExpResult{
	pub llvm_typ: llvm::Ty,
	//If llvm_typ is not Dynamic(_), then llvm_op has that type
	//if llvm_typ is Dynamic(_), then llvm_op is an i8*
	pub llvm_op: llvm::Operand,
	pub stream: Stream,
}
impl std::fmt::Debug for ExpResult {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		writeln!(f, "llvm_typ: {:?}", self.llvm_typ)?;
		writeln!(f, "llvm_op: {}", self.llvm_op)?;
		writeln!(f, "stream:")?;
		use Component::*;
		for component in self.stream.iter() { match component {
			Label(s) => writeln!(f, "label '{}'", s)?,
			Instr(dest, instr) => writeln!(f, "instr %{} = {}", dest, instr)?,
			Term(t) => writeln!(f, "term {}", t)?,
			GlobalString(s, gdecl) => writeln!(f, "GlobalString '{}', {}", s, gdecl)?
		}}
		Ok(())
	}
}

fn cmp_exp(e: &ast::Expr, ctxt: &Context, type_for_lit_nulls: Option<&llvm::Ty>) -> ExpResult { match e {
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
		llvm_typ: llvm::Ty::Int{bits: 1, signed: false},
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
			Component::GlobalString(global_string_ident.clone(), llvm::GlobalDecl::GString(s.clone())),
			Component::Instr(casted_local_ident.clone(), llvm::Instruction::Bitcast{
				original_typ: llvm::Ty::Ptr(Box::new(global_typ)),
				new_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
				op: llvm::Operand::Global(global_string_ident)
			})
		];
		ExpResult{
			llvm_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
			llvm_op: llvm::Operand::Local(casted_local_ident),
			stream,
		}
	},
	ast::Expr::Id(s) => cmp_lvalue_to_rvalue(e, &format!("{}_loaded", s) as &str, ctxt),
	ast::Expr::Deref(_) => cmp_lvalue_to_rvalue(e, "deref_loaded", ctxt),
	//llvm doesn't allow me to use extractvalue on an array (unless I know the idnex at compile time),
	//so I have to use getelementptr, and can't have arrays that aren't lvalues

	ast::Expr::Index(_,_) => cmp_lvalue_to_rvalue(e, "index_loaded", ctxt),
	//I added code here (rvalue Proj) to to handle dynamic structs. I may have to do a simiilar thing for rvalue Index,
	//but for now it seems to be working
	ast::Expr::Proj(base, field_name) => {
		/*
		Whenever this function is called, an "rvalue" is expected (i.e. the real struct,
		not a pointer to it), so this case only handles the rvalue case

		for something like v.x or f().x as an rvalue
		cmp_exp gets the struct itself, %v_loaded
		%field = extractvalue %vec_i32 %v_loaded, index

		for something like v->x as an rvalue
		cmp_exp(v) gets the pointer, %v_pointer
		%v_loaded = load %vec_i32, %vec_i32* %v_pointer
		%field = extractvalue %vec_i32 %v_loaded, index
		*/
		let mut base_result = cmp_exp(base as &ast::Expr, ctxt, None);
		let mut stream = base_result.stream;
		//The cases for Dynamic(Struct(s)) and Ptr(Dynamic(Struct(s))) are the same thing
		let mut base_type_param: Option<ast::Ty> = None;
		let (is_dynamic, base_is_ptr, struct_name) = match &base_result.llvm_typ {
			llvm::Ty::Dynamic(ast::Ty::Struct(s)) => (true, true, s.clone()),
			llvm::Ty::Dynamic(ast::Ty::GenericStruct{name: s, type_var: type_param}) => {
				base_type_param = Some(type_param.as_ref().clone());
				(true, true, s.clone())
			},
			llvm::Ty::NamedStruct(s) => (false, false, s.clone()),
			llvm::Ty::Ptr(boxed) => match boxed as &llvm::Ty {
				llvm::Ty::Dynamic(ast::Ty::Struct(s)) => (true, true, s.clone()),
				llvm::Ty::Dynamic(ast::Ty::GenericStruct{name: s, type_var: type_param}) => {
					base_type_param = Some(type_param.as_ref().clone());
					(true, true, s.clone())
				},
				llvm::Ty::NamedStruct(s) => (false, true, s.clone()),
				t => panic!("Proj base has llvm type Ptr({:?})", t)
			},
			t => panic!("Proj base has llvm type {:?}", t)
		};
		let fields: &[(String, ast::Ty)] = match ctxt.structs.get(&struct_name) {
			None => panic!("struct {} not in struct_context", &struct_name),
			Some(typechecker::StructType::NonGeneric(fields)) => fields as &[_],
			Some(typechecker::StructType::Generic{fields, ..}) => fields
		};
		let mut field_index: Option<usize> = None;
		for (i, (name, _src_ty)) in fields.iter().enumerate() {
			if name == field_name {
				field_index = Some(i);
				break;
			}
		}
		let field_index: usize = field_index.unwrap_or_else(|| panic!("field name {} not found in struct {}", field_name, struct_name));
		if is_dynamic {
			let preceding_fields_iter = fields.iter().take(field_index).map(|(_, t)| t.clone());
			let base_type_param = base_type_param.unwrap_or_else(|| ast::Ty::TypeVar("_should_not_happen".to_owned()));
			let (offset_op, offset_stream) = cmp_size_of_erased_struct(preceding_fields_iter, ctxt, &base_type_param);
			stream.extend(offset_stream);
			let ptr_offset_op = gensym("DST_offset");
			stream.push(Component::Instr(ptr_offset_op.clone(), llvm::Instruction::Gep{
				typ: llvm::Ty::Int{bits: 8, signed: false},
				base: base_result.llvm_op,
				offsets: vec![(llvm::Ty::Int{bits: 64, signed: false}, offset_op)]
			}));
			let field_typ: &ast::Ty = &fields[field_index].1;
			if !field_typ.is_DST(&ctxt.structs) {
				//only load from it if it is not a dynamic type
				//first, bitcast the i8* to the right type
				let llvm_field_typ = cmp_ty(field_typ, &ctxt.structs, 
					//if the base type is a regular struct that is dynamic, then don't need to pass
					//a replacement type here, otherwise the type parameter must be cmped
					match base_type_param {
						ast::Ty::TypeVar(s) if s == "_should_not_happen" => llvm::Ty::Void,
						_ => cmp_ty(&base_type_param, ctxt.structs, llvm::Ty::Void)
					}
				);
				let bitcasted_uid = gensym("proj_bitcast");
				stream.push(Component::Instr(bitcasted_uid.clone(), llvm::Instruction::Bitcast{
					original_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
					op: llvm::Operand::Local(ptr_offset_op),
					new_typ: llvm::Ty::Ptr(Box::new(llvm_field_typ.clone()))
				}));
				let loaded_uid = gensym("proj_load");
				stream.push(Component::Instr(loaded_uid.clone(), llvm::Instruction::Load{
					typ: llvm_field_typ.clone(),
					src: llvm::Operand::Local(bitcasted_uid)
				}));
				return ExpResult{
					llvm_typ: llvm_field_typ,
					llvm_op: llvm::Operand::Local(loaded_uid),
					stream
				}
			}
			//if the result is dynamic, it is already an i8*, so nothing needs to be done
			return ExpResult{
				llvm_typ: llvm::Ty::Dynamic(field_typ.clone()),
				llvm_op: llvm::Operand::Local(ptr_offset_op),
				stream
			}
		}
		use std::convert::TryFrom;
		let result_ty = cmp_ty(&fields[field_index].1, &ctxt.structs, llvm::Ty::Void);
		let field_index: u64 = u64::try_from(field_index).expect("could not convert from usize to u64");
		let base_loaded_op: llvm::Operand;
		if base_is_ptr {
			base_result.llvm_typ = base_result.llvm_typ.remove_ptr();
			let base_loaded_uid = gensym("base_loaded");
			base_loaded_op = llvm::Operand::Local(base_loaded_uid.clone());
			stream.push(Component::Instr(base_loaded_uid, llvm::Instruction::Load{
				typ: base_result.llvm_typ.clone(),
				src: base_result.llvm_op
			}));
		} else {
			base_loaded_op = base_result.llvm_op;
		}
		let extracted_uid = gensym("extract");
		stream.push(Component::Instr(extracted_uid.clone(), llvm::Instruction::Extract{
			typ: base_result.llvm_typ,
			base: base_loaded_op,
			offset: field_index
		}));
		ExpResult{
			llvm_typ: result_ty,
			llvm_op: llvm::Operand::Local(extracted_uid),
			stream
		}
	},
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
		if exprs.is_empty() {
			llvm_type_of_first_expr = llvm::Ty::Int{bits: 64, signed: true};
		} else {
			//ignoring the possibility of the first expr being a LitNull, not setting type_for_lit_nulls
			let mut init_0_result = cmp_exp(&exprs[0], ctxt, type_for_lit_nulls);
			llvm_type_of_first_expr = init_0_result.llvm_typ;
			stream.append(&mut init_0_result.stream);
			expr_operands.push(init_0_result.llvm_op);
			let new_type_for_lit_nulls = Some(&llvm_type_of_first_expr);
			for init in exprs[1..].iter() {
				let mut result = cmp_exp(init, ctxt, new_type_for_lit_nulls);
				debug_assert_eq!(llvm_type_of_first_expr, result.llvm_typ);
				stream.append(&mut result.stream);
				expr_operands.push(result.llvm_op);
			}
		}
		let llvm_array_type = llvm::Ty::Array{length: exprs.len(), typ: Box::new(llvm_type_of_first_expr.clone())};
		let llvm_ptr_type = llvm::Ty::Ptr(Box::new(llvm_type_of_first_expr.clone()));
		let arr_base = gensym("arr_base");
		let arr_as_ptr = gensym("arr_as_ptr");
		stream.push(Component::Instr(arr_base.clone(), llvm::Instruction::Alloca(llvm_array_type.clone(), llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 1}), None)));
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
	ast::Expr::Cast(new_type, src) => {
		let mut src_result = cmp_exp(src as &ast::Expr, ctxt, Some(&llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))));
		let new_llvm_typ = cmp_ty(new_type, &ctxt.structs, llvm::Ty::Void);
		use llvm::Ty::*;
		match (&new_llvm_typ, &src_result.llvm_typ) {
			(Int{bits: new_bits, signed: _new_signed}, Int{bits: old_bits, signed: old_signed}) => {
				if new_bits == old_bits {
					//llvm does not care about the signs, but I do, so set the signedness to whatever the new type is
					src_result.llvm_typ = new_llvm_typ.clone();
					return src_result;
				}
				if new_bits < old_bits {
					let truncated_uid = gensym("truncated");
					let mut stream = src_result.stream;
					stream.push(Component::Instr(truncated_uid.clone(), llvm::Instruction::Trunc{
						old_bits: *old_bits,
						op: src_result.llvm_op,
						new_bits: *new_bits,
					}));
					ExpResult{
						llvm_typ: new_llvm_typ,
						llvm_op: llvm::Operand::Local(truncated_uid),
						stream
					}
				} else {
					let extended_uid = gensym("extended");
					let mut stream = src_result.stream;
					stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
						old_bits: *old_bits,
						op: src_result.llvm_op,
						new_bits: *new_bits,
						signed: *old_signed
					}));
					ExpResult{
						llvm_typ: new_llvm_typ,
						llvm_op: llvm::Operand::Local(extended_uid),
						stream
					}
				}
			},
			(Float32, Float32) | (Float64, Float64) => src_result,
			(Float32, Float64) => {
				let truncated_uid = gensym("float_truncated");
				let mut stream = src_result.stream;
				stream.push(Component::Instr(truncated_uid.clone(), 
					llvm::Instruction::FloatTrunc(src_result.llvm_op)
				));
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(truncated_uid),
					stream
				}
			},
			(Float64, Float32) => {
				let extended_uid = gensym("float_extended");
				let mut stream = src_result.stream;
				stream.push(Component::Instr(extended_uid.clone(), 
					llvm::Instruction::FloatExt(src_result.llvm_op)
				));
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(extended_uid),
					stream
				}
			},
			(Float32, Int{bits, signed}) | (Float64, Int{bits, signed}) => {
				let converted_uid = gensym("int_to_float");
				let mut stream = src_result.stream;
				if *signed {
					stream.push(Component::Instr(converted_uid.clone(), llvm::Instruction::SignedToFloat{
						old_bits: *bits,
						op: src_result.llvm_op,
						result_is_64_bit: matches!(new_llvm_typ, Float64)
					}));
				} else {
					stream.push(Component::Instr(converted_uid.clone(), llvm::Instruction::UnsignedToFloat{
						old_bits: *bits,
						op: src_result.llvm_op,
						result_is_64_bit: matches!(new_llvm_typ, Float64)
					}));
				}
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(converted_uid),
					stream
				}
			},
			(Int{bits, signed}, Float32) | (Int{bits, signed}, Float64) => {
				let converted_uid = gensym("float_to_int");
				let mut stream = src_result.stream;
				if *signed {
					stream.push(Component::Instr(converted_uid.clone(), llvm::Instruction::FloatToSigned{
						new_bits: *bits,
						op: src_result.llvm_op,
						src_is_64_bit: matches!(new_llvm_typ, Float64)
					}));
				} else {
					stream.push(Component::Instr(converted_uid.clone(), llvm::Instruction::FloatToUnsigned{
						new_bits: *bits,
						op: src_result.llvm_op,
						src_is_64_bit: matches!(new_llvm_typ, Float64)
					}));
				}
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(converted_uid),
					stream
				}
			},
			(Ptr(_), Ptr(_)) => {
				let casted_uid = gensym("ptr_cast");
				let mut stream = src_result.stream;
				stream.push(Component::Instr(casted_uid.clone(), llvm::Instruction::Bitcast{
					original_typ: src_result.llvm_typ,
					op: src_result.llvm_op,
					new_typ: new_llvm_typ.clone()
				}));
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(casted_uid),
					stream
				}
			}
			(new, old) => panic!("trying to cast from {:?} to {:?}", old, new)
		}
	},
	ast::Expr::Binop(left, bop, right) => {
		let left_result = cmp_exp(left, ctxt, Some(&llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))));
		let mut right_result = cmp_exp(right, ctxt, Some(&llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))));
		let mut stream = left_result.stream;
		stream.append(&mut right_result.stream);
		use ast::BinaryOp::*;
		match (bop, &left_result.llvm_typ, &right_result.llvm_typ) {
			//Arithmetic between Ints
			(_, llvm::Ty::Int{bits: l_bits, signed: l_signed}, llvm::Ty::Int{bits: r_bits, signed: r_signed})
			if matches!(bop, Add | Sub | Mul | Div | Mod | And | Or | Bitand | Bitor | Bitxor | Shl | Shr | Sar)=> {
				let uid = gensym("bool_op");
				let mut extended_left_op = left_result.llvm_op;
				let mut extended_right_op = right_result.llvm_op;
				use std::cmp::Ordering;
				match l_bits.cmp(r_bits) {
					Ordering::Less => {
						let extended_uid = gensym("extend_for_binop");
						stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
							old_bits: *l_bits,
							op: extended_left_op,
							new_bits: *r_bits,
							signed: *l_signed
						}));
						extended_left_op = llvm::Operand::Local(extended_uid);
					},
					Ordering::Greater => {
						let extended_uid = gensym("extend_for_binop");
						stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
							old_bits: *r_bits,
							op: extended_right_op,
							new_bits: *l_bits,
							signed: *r_signed
						}));
						extended_right_op = llvm::Operand::Local(extended_uid);
					},
					Ordering::Equal => ()
				};
				stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
					op: cmp_binary_op(bop),
					typ: llvm::Ty::Int{bits: std::cmp::max(*l_bits, *r_bits), signed: false},
					left: extended_left_op,
					right: extended_right_op
				}));
				ExpResult{
					llvm_typ: left_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
					stream
				}
			},
			//Comparisons between Ints
			(cond_op, llvm::Ty::Int{bits: l_bits, signed}, llvm::Ty::Int{bits: r_bits, ..}) => {
				let uid = gensym("cmp");
				let mut extended_left_op = left_result.llvm_op;
				let mut extended_right_op = right_result.llvm_op;
				use std::cmp::Ordering;
				match l_bits.cmp(r_bits) {
					Ordering::Less => {
						let extended_uid = gensym("extend_for_binop");
						stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
							old_bits: *l_bits,
							op: extended_left_op,
							new_bits: *r_bits,
							signed: *signed
						}));
						extended_left_op = llvm::Operand::Local(extended_uid);
					},
					Ordering::Greater => {
						let extended_uid = gensym("extend_for_binop");
						stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
							old_bits: *r_bits,
							op: extended_right_op,
							new_bits: *l_bits,
							signed: *signed
						}));
						extended_right_op = llvm::Operand::Local(extended_uid);
					},
					Ordering::Equal => ()
				};
				stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
					cond: cmp_cond_op(cond_op),
					typ: llvm::Ty::Int{bits: std::cmp::max(*l_bits, *r_bits), signed: *signed},
					left: extended_left_op,
					right: extended_right_op
				}));
				ExpResult{
					llvm_typ: llvm::Ty::Int{bits: 1, signed: false},
					llvm_op: llvm::Operand::Local(uid),
					stream
				}
			},
			//Arithmetic and Comparisons between Floats
			(_, llvm::Ty::Float32, llvm::Ty::Float32) | (_, llvm::Ty::Float64, llvm::Ty::Float64) => match bop {
				Equ | Neq | Gt | Gte | Lt | Lte => {
					let uid = gensym("float_cmp");
					stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
						cond: cmp_cond_op(bop),
						typ: left_result.llvm_typ,
						left: left_result.llvm_op,
						right: right_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Int{bits: 1, signed: false},
						llvm_op: llvm::Operand::Local(uid),
						stream
					}
				},
				arith => {
					let uid = gensym("float_arith");
					stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
						op: cmp_binary_op(arith),
						typ: left_result.llvm_typ,
						left: left_result.llvm_op,
						right: right_result.llvm_op
					}));
					ExpResult{
						llvm_typ: right_result.llvm_typ,
						llvm_op: llvm::Operand::Local(uid),
						stream
					}
				}
			},
			(_, llvm::Ty::Float32, llvm::Ty::Float64) => match bop {
				Equ | Neq | Gt | Gte | Lt | Lte => {
					let uid = gensym("float_cmp");
					let extended_uid = gensym("float_ext");
					stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::FloatExt(left_result.llvm_op)));
					stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
						cond: cmp_cond_op(bop),
						typ: llvm::Ty::Float64,
						left: llvm::Operand::Local(extended_uid),
						right: right_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Float64,
						llvm_op: llvm::Operand::Local(uid),
						stream
					}
				},
				_arith => {
					let uid = gensym("float_arith");
					let extended_uid = gensym("float_ext");
					stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::FloatExt(left_result.llvm_op)));
					stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
						op: cmp_binary_op(bop),
						typ: llvm::Ty::Float64,
						left: llvm::Operand::Local(extended_uid),
						right: right_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Float64,
						llvm_op: llvm::Operand::Local(uid),
						stream
					}
				}
			},
			(_, llvm::Ty::Float64, llvm::Ty::Float32) => match bop {
				Equ | Neq | Gt | Gte | Lt | Lte => {
					let uid = gensym("float_cmp");
					let extended_uid = gensym("float_ext");
					stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::FloatExt(right_result.llvm_op)));
					stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
						cond: cmp_cond_op(bop),
						typ: llvm::Ty::Float64,
						right: llvm::Operand::Local(extended_uid),
						left: left_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Float64,
						llvm_op: llvm::Operand::Local(uid),
						stream
					}
				},
				_arith => {
					let uid = gensym("float_arith");
					let extended_uid = gensym("float_ext");
					stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::FloatExt(right_result.llvm_op)));
					stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
						op: cmp_binary_op(bop),
						typ: llvm::Ty::Float64,
						right: llvm::Operand::Local(extended_uid),
						left: left_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Float64,
						llvm_op: llvm::Operand::Local(uid),
						stream
					}
				}
			},
			//Pointer arithmetic
			(Add, llvm::Ty::Ptr(_), llvm::Ty::Int{bits, ..}) | 
			(Sub, llvm::Ty::Ptr(_), llvm::Ty::Int{bits, ..}) => {
				let ptr_arith_uid = gensym("ptr_arith");
				let offset_op;
				if matches!(bop, ast::BinaryOp::Sub) {
					let negated_offset_uid = gensym("negated_offset");
					stream.push(Component::Instr(negated_offset_uid.clone(), llvm::Instruction::Binop{
						op: llvm::BinaryOp::Mul,
						typ: right_result.llvm_typ.clone(),
						left: right_result.llvm_op,
						right: llvm::Operand::Const(llvm::Constant::SInt{bits: *bits, val: -1})
					}));
					offset_op = llvm::Operand::Local(negated_offset_uid);
				} else {
					offset_op = right_result.llvm_op;
				}
				stream.push(Component::Instr(ptr_arith_uid.clone(), llvm::Instruction::Gep{
					typ: left_result.llvm_typ.clone(),
					base: left_result.llvm_op,
					offsets: vec![
						(right_result.llvm_typ, offset_op)
					]
				}));
				ExpResult{
					llvm_typ: left_result.llvm_typ,
					llvm_op: llvm::Operand::Local(ptr_arith_uid),
					stream
				}
			},
			//Pointer Comparison
			(_cond_op, llvm::Ty::Ptr(_), llvm::Ty::Ptr(_)) => {
				let uid = gensym("ptr_cmp");
				stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
					cond: cmp_cond_op(bop),
					typ: left_result.llvm_typ,
					left: left_result.llvm_op,
					right: right_result.llvm_op
				}));
				ExpResult{
					llvm_typ: llvm::Ty::Int{bits: 1, signed: false},
					llvm_op: llvm::Operand::Local(uid),
					stream
				}
			},
			_ => panic!("cannot use binop {:?} on llvm types {:?} and {:?}", bop, left_result.llvm_typ, right_result.llvm_typ)
		}
	},
	ast::Expr::Unop(uop, base) => {
		let base_result = cmp_exp(base, ctxt, Some(&llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))));
		let mut stream = base_result.stream;
		use ast::UnaryOp::*;
		match (uop, &base_result.llvm_typ) {
			(Neg, llvm::Ty::Int{bits, signed}) => {
				debug_assert!(*signed, "negating an unsigned int");
				let uid = gensym("neg_int");
				stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
					op: llvm::BinaryOp::Mul,
					typ: llvm::Ty::Int{bits: *bits, signed: *signed},
					left: base_result.llvm_op,
					right: llvm::Operand::Const(llvm::Constant::SInt{bits: *bits, val: -1})
				}));
				ExpResult{
					llvm_typ: base_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
					stream
				}
			},
			(Neg, llvm::Ty::Float32) | (Neg, llvm::Ty::Float64) => {
				let uid = gensym("neg_float");
				stream.push(Component::Instr(uid.clone(), llvm::Instruction::FloatNeg{
					is_64_bit: base_result.llvm_typ == llvm::Ty::Float64,
					op: base_result.llvm_op
				}));
				ExpResult{
					llvm_typ: base_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
					stream
				}
			},
			(Neg, t) => panic!("neg of type {:?}", t),
			(Lognot, llvm::Ty::Int{bits, signed}) => {
				debug_assert!(*bits == 1 && !signed);
				let uid = gensym("lognot");
				stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
					op: llvm::BinaryOp::Sub,
					typ: llvm::Ty::Int{bits: 1, signed: false},
					left: llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: 1}),
					right: base_result.llvm_op
				}));
				ExpResult{
					llvm_typ: base_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
					stream
				}
			},
			(Lognot, t) => panic!("neg of type {:?}", t),
			(Bitnot, llvm::Ty::Int{bits, signed}) => {
				let uid = gensym("bitnot");
				stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
					op: llvm::BinaryOp::Bitxor,
					typ: llvm::Ty::Int{bits: *bits, signed: *signed},
					left: base_result.llvm_op,
					right: llvm::Operand::Const(llvm::Constant::SInt{bits: *bits, val: -1})
				}));
				ExpResult{
					llvm_typ: base_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
					stream
				}
			},
			(Bitnot, t) => panic!("lognot of type {:?}", t)
		}
	},
	ast::Expr::GetRef(boxed) => {
		let mut result = cmp_lvalue(boxed as &ast::Expr, ctxt);
		result.llvm_typ = llvm::Ty::Ptr(Box::new(result.llvm_typ));
		result
	},
	ast::Expr::Sizeof(t) => {
		if t.is_DST(ctxt.structs) {
			//t is dynamically sized, and it is either a GenericStruct, Struct, or Array
			match t {
				ast::Ty::Array{length, typ} => {
					let mut base_typ_result = cmp_exp(&ast::Expr::Sizeof((typ as &ast::Ty).clone()), ctxt, None);
					let mul_name = gensym("sizeof_arr_mul");
					base_typ_result.stream.push(Component::Instr(mul_name.clone(), llvm::Instruction::Binop{
						op: llvm::BinaryOp::Mul,
						typ: llvm::Ty::Int{bits: 64, signed: false},
						left: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: *length}),
						right: base_typ_result.llvm_op
					}));
					base_typ_result.llvm_op = llvm::Operand::Local(mul_name);
					return base_typ_result;
				},
				//if a struct contains an erased struct, it also has a dynamic size
				ast::Ty::Struct(name) => {
					if let typechecker::StructType::NonGeneric(fields) = ctxt.structs.get(name).unwrap() {
						//I need to pass some type param to cmp_size_of_erased_struct here, using a TypeVar should ensure a crash rather than a miscompile
						let (llvm_op, stream) = cmp_size_of_erased_struct(fields.iter().map(|(_, t)| t.clone()), ctxt, &ast::Ty::TypeVar("_should_not_happen".to_owned()));
						return ExpResult{
							llvm_op,
							llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
							stream
						};
					} else {
						panic!("struct context contains generic struct for non-generic struct {}", name);
					}
				},
				ast::Ty::GenericStruct{type_var: type_param, name} => {
					if let typechecker::StructType::Generic{mode: ast::PolymorphMode::Erased, fields, ..} = ctxt.structs.get(name).unwrap() {
						let (llvm_op, stream) = cmp_size_of_erased_struct(fields.iter().map(|(_, t)| t.clone()), ctxt, type_param);
						return ExpResult {
							llvm_op,
							llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
							stream
						}
					} else {
						panic!("struct context does not contain an erased struct for '{}'", name);
					}
				},
				_ => panic!("type {} cannot contain an erased struct", t)
			}
		};
		let size_uid = gensym("sizeof");
		let size_int_uid = gensym("sizeof_int");
		let llvm_typ = cmp_ty(t, &ctxt.structs, llvm::Ty::Void);
		let llvm_ptr_typ = llvm::Ty::Ptr(Box::new(llvm_typ.clone()));
		let stream = vec![
			Component::Instr(size_uid.clone(), llvm::Instruction::Gep{
				typ: llvm_typ.clone(),
				base: llvm::Operand::Const(llvm::Constant::Null(llvm_typ)),
				offsets: vec![
					(llvm::Ty::Int{bits: 32, signed: true}, llvm::Operand::Const(llvm::Constant::SInt{bits: 32, val: 1}))
				]
			}),
			Component::Instr(size_int_uid.clone(), llvm::Instruction::PtrToInt{
				ptr_ty: llvm_ptr_typ,
				op: llvm::Operand::Local(size_uid)
			})
		];
		ExpResult{
			llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
			llvm_op: llvm::Operand::Local(size_int_uid),
			stream
		}
	},
	ast::Expr::Call(func_name, args) => cmp_call(func_name.clone(), args, ctxt),
	ast::Expr::GenericCall{..} => panic!("generic_call not implemented yet")
}}

//in an erased function, this is an implicit variable (of type u64) that stores the size of the current type variable
const PARAM_SIZE_NAME: &str = "__param_size";

//in a function that returns a DST, this is an implicit variable that stores the address where the return
//value should be written to. It's actual llvm type is i8*.
const RET_LOC_NAME: &str = "__ret_loc";

//the name of the builting llvm memcpy function
const LLVM_MEMCPY_FUNC_NAME: &str = "llvm.memcpy.p0i8.p0i8.i64";

//This function returns code that computes the size of an erased struct. This function can be used
//to find the offset of a field in a struct by calling it with only the fields that come before the desired field
pub fn cmp_size_of_erased_struct<TypeIter: IntoIterator<Item = ast::Ty>>(fields: TypeIter, ctxt: &Context, type_param: &ast::Ty) -> (llvm::Operand, Stream) {
	/*
	%acc = 0 + 0
	%acc = %acc + cmp sizeof fields[0]
	%acc = %acc + 7
	%acc = %acc & ~7u64
	%acc = %acc + cmp sizeof fields[1]
	%acc = %acc + 7
	%acc = %acc & ~8u64
	*/
	let mut stream = Vec::new();
	let mut acc_name = gensym("sizeof_acc");
	stream.push(Component::Instr(acc_name.clone(), llvm::Instruction::Binop{
		op: llvm::BinaryOp::Add,
		typ: llvm::Ty::Int{bits: 64, signed: false},
		left: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 0}),
		right: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 0}),
	}));
	for mut field_ty in fields {
		let added_acc_name = gensym("sizeof_acc");
		field_ty.replace_type_var_with(type_param);
		let sizeof_result = cmp_exp(&ast::Expr::Sizeof(field_ty), ctxt, None);
		stream.extend(sizeof_result.stream);
		stream.push(Component::Instr(added_acc_name.clone(), llvm::Instruction::Binop{
			op: llvm::BinaryOp::Add,
			typ: llvm::Ty::Int{bits: 64, signed: false},
			left: llvm::Operand::Local(acc_name),
			right: sizeof_result.llvm_op
		}));
		let add7_acc_name = gensym("sizeof_acc");
		stream.push(Component::Instr(add7_acc_name.clone(), llvm::Instruction::Binop{
			op: llvm::BinaryOp::Add,
			typ: llvm::Ty::Int{bits: 64, signed: false},
			left: llvm::Operand::Local(added_acc_name),
			right: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 7u64})
		}));
		let anded_acc_name = gensym("sizeof_acc");
		stream.push(Component::Instr(anded_acc_name.clone(), llvm::Instruction::Binop{
			op: llvm::BinaryOp::Bitand,
			typ: llvm::Ty::Int{bits: 64, signed: false},
			left: llvm::Operand::Local(add7_acc_name),
			right: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: !7u64})
		}));
		acc_name = anded_acc_name;
	}
	(llvm::Operand::Local(acc_name), stream)
}

fn cmp_call(func_name: String, args: &[ast::Expr], ctxt: &Context) -> ExpResult {
	let mut stream: Vec<Component> = Vec::with_capacity(args.len());
	let mut arg_ty_ops: Vec<(llvm::Ty, llvm::Operand)> = Vec::with_capacity(args.len());
	let printf_expected_args_vec;
	let printf_ret_ty;
	let (return_type, expected_arg_types) = match ctxt.funcs.get(func_name.as_str()) {
		Some(typechecker::FuncType::NonGeneric{return_type, args}) => (return_type, args),
		None => {
			if typechecker::PRINTF_FAMILY.contains(&func_name.as_str()){
				printf_ret_ty = Some(ast::Ty::Int{size: ast::IntSize::Size32, signed: true});
				//create an iterator that continuously yields void*, then take the first n from it
				printf_expected_args_vec = Some(ast::Ty::Ptr(None)).into_iter()
					.cycle()
					.take(args.len())
					.collect();
				(&printf_ret_ty, &printf_expected_args_vec)
			} else {
				panic!("function {} does not exist", func_name)
			}
		}
		Some(typechecker::FuncType::Generic{..}) => panic!("function {} is generic", func_name)
	};
	for (arg, expected_ty) in args.iter().zip(expected_arg_types) {
		//only need to compute this if the arg is a LitNull
		let type_for_lit_nulls = match arg {
			ast::Expr::LitNull => Some(cmp_ty(expected_ty, &ctxt.structs, llvm::Ty::Void)),
			_ => None
		};
		let mut arg_result = cmp_exp(arg, ctxt, type_for_lit_nulls.as_ref());
		arg_ty_ops.push((arg_result.llvm_typ, arg_result.llvm_op));
		stream.append(&mut arg_result.stream);
	}
	let uid = gensym("call");
	let mut dst_result_uid: Option<String> = None;
	let (result_is_dst, llvm_ret_ty) = match return_type {
		None => (false, llvm::Ty::Void),
		Some(t) if t.is_DST(&ctxt.structs) => {
			//compute the size of this type, alloca this much space, pass the pointer as an extra arg
			let ExpResult{llvm_op: sizeof_op, stream: mut sizeof_stream, ..} = cmp_exp(&ast::Expr::Sizeof(t.clone()), ctxt, None);
			stream.append(&mut sizeof_stream);
			let result_addr_uid = gensym("DST_retval_result");
			dst_result_uid = Some(result_addr_uid.clone());
			stream.push(Component::Instr(result_addr_uid.clone(), llvm::Instruction::Alloca(
				llvm::Ty::Int{bits: 8, signed: false}, sizeof_op, Some(8)
			)));
			arg_ty_ops.push( (llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})), llvm::Operand::Local(result_addr_uid)) );
			(true, llvm::Ty::Void)
		},
		Some(t) => (false, cmp_ty(t, &ctxt.structs, llvm::Ty::Void))
	};
	stream.push(Component::Instr(uid.clone(), llvm::Instruction::Call{
		func_name: func_name.clone(),
		ret_typ: llvm_ret_ty.clone(),
		args: arg_ty_ops
	}));
	if result_is_dst {
		ExpResult{
			llvm_typ: llvm::Ty::Dynamic(return_type.as_ref().unwrap().clone()),
			llvm_op: llvm::Operand::Local(dst_result_uid.unwrap()),
			stream
		}
	} else {
		ExpResult{
			llvm_typ: llvm_ret_ty,
			llvm_op: llvm::Operand::Local(uid),
			stream
		}
	}
}

//the op this function returns is a pointer to where the data is stored
//the llvm::Ty this function returns is the type of the thing being pointed to, it may not be a Ptr
fn cmp_lvalue(e: &ast::Expr, ctxt: &Context) -> ExpResult { match e {
	ast::Expr::Id(s) => {
		let (ll_ty, ll_op) = ctxt.get_var(s);
		ExpResult{
			llvm_typ: ll_ty.clone(),
			llvm_op: ll_op.clone(),
			stream: vec![]
		}
	},
	ast::Expr::Index(base, index) => {
		let mut base_lvalue_result;
		if !matches!(base as &ast::Expr, ast::Expr::Id(_) | ast::Expr::Index(_,_) | ast::Expr::Proj(_,_) | ast::Expr::Deref(_)) {
			//if base is a function call, then it must return a pointer
			base_lvalue_result = cmp_exp(base as &ast::Expr, ctxt, None);
		} else {
			//if base is a potential lvalue, then cmp it as an lvalue, see what it's type is,
			//and potentially load from it if its type is a pointer
			base_lvalue_result = cmp_lvalue(base as &ast::Expr, ctxt);
			match &base_lvalue_result.llvm_typ {
				llvm::Ty::Dynamic(ast::Ty::Array{typ: nested_dynamic_type, ..}) => {
					//need to change base_lvalue_result to make its llvm_typ a Ptr(Dynamic(nested_dynamic_type))
					//don't have to emit any instructions, because it would just bitcast from i8* to i8*
					base_lvalue_result.llvm_typ = llvm::Ty::Ptr(Box::new(llvm::Ty::Dynamic(nested_dynamic_type.as_ref().clone())));
				},
				//if base is an array, convert it to a pointer to the first element
				llvm::Ty::Array{typ, ..} => {
					let decay_id = gensym("arr_decay");
					base_lvalue_result.stream.push(Component::Instr(decay_id.clone(), llvm::Instruction::Bitcast{
						original_typ: llvm::Ty::Ptr(Box::new(base_lvalue_result.llvm_typ.clone())),
						op: base_lvalue_result.llvm_op,
						new_typ: llvm::Ty::Ptr(typ.clone())
					}));
					base_lvalue_result.llvm_typ = llvm::Ty::Ptr(typ.clone());
					base_lvalue_result.llvm_op = llvm::Operand::Local(decay_id);
				},
				//if base is a Ptr, convert base_lvalue_result directly to the pointer itself, similar to what cmp_lvalue_to_rvalue does
				llvm::Ty::Ptr(_) => {
					let loaded_id = gensym("index_load");
					base_lvalue_result.stream.push(Component::Instr(loaded_id.clone(), llvm::Instruction::Load{
						typ: base_lvalue_result.llvm_typ.clone(),
						src: base_lvalue_result.llvm_op
					}));
					base_lvalue_result.llvm_op = llvm::Operand::Local(loaded_id);
				},
				_other => panic!("base_lvalue_result is {:?}, e = {:?}", base_lvalue_result, e)
				//other => panic!("base_lvalue_result has llvm_typ {}, e = {:?}", other, e)
			};
		}
		//base_lvalue_result is now the address of the first element of the array
		let mut stream = base_lvalue_result.stream;
		let mut index_result = cmp_exp(index as &ast::Expr, ctxt, None);
		stream.append(&mut index_result.stream);
		let result_op = gensym("index_offset");
		let result_typ = base_lvalue_result.llvm_typ.remove_ptr();
		if let llvm::Ty::Dynamic(dst) = &result_typ {
			let ExpResult{llvm_op: sizeof_op, stream: mut sizeof_stream, ..} = cmp_exp(&ast::Expr::Sizeof(dst.clone()), ctxt, None);
			stream.append(&mut sizeof_stream);
			let (index_result_bits, signed) = match index_result.llvm_typ {
				llvm::Ty::Int{bits, signed} => (bits, signed),
				_ => panic!("array index's llvm_typ is not an integer")
			};
			if index_result_bits < 64 {
				let extended_uid = gensym("extended");
				stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
					old_bits: index_result_bits,
					op: index_result.llvm_op,
					new_bits: 64,
					signed
				}));
				index_result.llvm_op = llvm::Operand::Local(extended_uid);
				index_result.llvm_typ = llvm::Ty::Int{bits: 64, signed};
			}
			let mul_uid = gensym("dyn_index_mul");
			stream.push(Component::Instr(mul_uid.clone(), llvm::Instruction::Binop{
				op: llvm::BinaryOp::Mul,
				typ: index_result.llvm_typ,
				left: index_result.llvm_op,
				right: sizeof_op
			}));
			let add_uid = gensym("dyn_index_add");
			stream.push(Component::Instr(add_uid.clone(), llvm::Instruction::Gep{
				typ: llvm::Ty::Int{bits: 8, signed: false},
				base: base_lvalue_result.llvm_op,
				offsets: vec![(llvm::Ty::Int{bits: 64, signed: false}, llvm::Operand::Local(mul_uid))]
			}));
			ExpResult{
				llvm_typ: result_typ,
				llvm_op: llvm::Operand::Local(add_uid),
				stream
			}
		} else {
			stream.push(Component::Instr(result_op.clone(), llvm::Instruction::Gep{
				typ: result_typ.clone(),
				base: base_lvalue_result.llvm_op,
				offsets: vec![(index_result.llvm_typ, index_result.llvm_op)]
			}));
			ExpResult{
				llvm_typ: result_typ,
				llvm_op: llvm::Operand::Local(result_op),
				stream
			}
		}

	},
	ast::Expr::Proj(base, field_name) => {
		/*
		
		for something like v.x as an lvalue, cmp_lvalue(v) gets the address of the struct, %v_addr
		%field_addr = getelementptr %vec_i32, %vec_i32* %v_addr, 0, i64 index

		for something like v->x as an lvalue, cmp_exp(v) gets the pointer, %v_addr
		%field_addr = getelementptr %vec_i32, %vec_i32* %v_addr, 0, i64 index
		how to tell whether to use cmp_value or cmp_exp?
		if base is not a valid lvalue (function call, etc), or the Ty returned by cmp_lvalue(base)
		is a Ptr, then copypaste code from cmp_lvalue_to_rvalue to turn this into the
		result of calling cmp_exp, then use second method
		*/
		let mut base_lvalue_result;
		if !matches!(base as &ast::Expr, ast::Expr::Id(_) | ast::Expr::Index(_,_) | ast::Expr::Proj(_,_) | ast::Expr::Deref(_)) {
			//something like f()->field
			//if doing something like null.field, the typechecker will catch this, so the None here is ok
			base_lvalue_result = cmp_exp(base as &ast::Expr, ctxt, None);
		} else {
			base_lvalue_result = cmp_lvalue(base as &ast::Expr, ctxt);
			match &base_lvalue_result.llvm_typ {
				llvm::Ty::Dynamic(_) => (), //if loading from the base operand would yield a DST, don't do anything
				llvm::Ty::NamedStruct(_) => (), //if base points to a struct directly, don't do anything
				llvm::Ty::Ptr(boxed) => match boxed as &llvm::Ty {
					llvm::Ty::NamedStruct(_) | llvm::Ty::Dynamic(_) => {
						let loaded_id = gensym("struct_deref");
						base_lvalue_result.stream.push(Component::Instr(loaded_id.clone(), llvm::Instruction::Load{
							typ: base_lvalue_result.llvm_typ.clone(),
							src: base_lvalue_result.llvm_op
						}));
						base_lvalue_result.llvm_op = llvm::Operand::Local(loaded_id);
					}
					t => panic!("Proj base has llvm type Ptr({:?})", t)
				}
				t => panic!("Proj base has llvm type {:?}", t)
			};
		}
		let mut is_dynamic = false;
		//if the base has type struct A@<u64>, then base_type_param will be set to u64
		let mut base_type_param: Option<ast::Ty> = None;
		let struct_name: String = match &base_lvalue_result.llvm_typ {
			llvm::Ty::Dynamic(t) => {
				is_dynamic = true;
				match t {
					ast::Ty::Struct(s) => s.clone(),
					ast::Ty::GenericStruct{name, type_var: type_param} => {
						base_type_param = Some((type_param as &ast::Ty).clone());
						name.clone()
					},
					t => panic!("Cannot do a dynamic proj off of type {:?}", t)
				}
			},
			llvm::Ty::NamedStruct(s) => s.clone(),
			llvm::Ty::Ptr(boxed) => match boxed as &llvm::Ty {
				llvm::Ty::Dynamic(t) => {
					is_dynamic = true;
					match t {
						ast::Ty::Struct(s) => s.clone(),
						ast::Ty::GenericStruct{name, type_var: type_param} => {
							base_type_param = Some((type_param as &ast::Ty).clone());
							name.clone()
						},
						t => panic!("Cannot do a dynamic proj off of type {:?}", t)
					}
				}
				llvm::Ty::NamedStruct(s) => s.clone(),
				t => panic!("Proj base has llvm type Ptr({:?})", t)
			}
			t => panic!("Proj base has llvm type {:?}", t)
		};
		//base_lvalue_result is now the address of the struct, just need to do one more Gep
		let fields: &[(String, ast::Ty)] = match ctxt.structs.get(&struct_name) {
			None => panic!("struct {} not in struct_context", &struct_name),
			Some(typechecker::StructType::NonGeneric(fields)) => fields as &[_],
			Some(typechecker::StructType::Generic{fields, ..}) => {
				fields
			}
		};
		let mut field_index: Option<usize> = None;
		for (i, (name, _src_ty)) in fields.iter().enumerate() {
			if name == field_name {
				field_index = Some(i);
				break;
			}
		}
		let field_index: usize = field_index.unwrap_or_else(|| panic!("field name {} not found in struct {}", field_name, struct_name));
		if is_dynamic {
			let preceding_fields_iter = fields.iter().take(field_index).map(|(_, t)| t.clone());
			let base_type_param = base_type_param.unwrap_or_else(|| ast::Ty::TypeVar("_should_not_happen".to_owned()));
			let (offset_op, offset_stream) = cmp_size_of_erased_struct(preceding_fields_iter, ctxt, &base_type_param);
			base_lvalue_result.stream.extend(offset_stream);
			let ptr_offset_op = gensym("DST_offset");
			base_lvalue_result.stream.push(Component::Instr(ptr_offset_op.clone(), llvm::Instruction::Gep{
				typ: llvm::Ty::Int{bits: 8, signed: false},
				base: base_lvalue_result.llvm_op,
				offsets: vec![(llvm::Ty::Int{bits: 64, signed: false}, offset_op)]
			}));
			let field_type: &ast::Ty = &fields[field_index].1;
			base_lvalue_result.llvm_typ = cmp_ty(field_type, ctxt.structs,
				//if the base type is a regular struct that is dynamic, then don't need to pass a
				//replacement type here, otherwise the type parameter must be cmped
				match base_type_param {
					ast::Ty::TypeVar(s) if s == "_should_not_happen" => llvm::Ty::Void,
					_ => cmp_ty(&base_type_param, ctxt.structs, llvm::Ty::Void)
				}
			);
			let bitcasted_uid = gensym("DST_proj_bitcast");
			base_lvalue_result.stream.push(Component::Instr(bitcasted_uid.clone(), llvm::Instruction::Bitcast{
				original_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
				op: llvm::Operand::Local(ptr_offset_op),
				new_typ: if matches!(base_lvalue_result.llvm_typ, llvm::Ty::Dynamic(_)) {
					llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))
				} else {
					llvm::Ty::Ptr(Box::new(base_lvalue_result.llvm_typ.clone()))
				}
			}));
			base_lvalue_result.llvm_op = llvm::Operand::Local(bitcasted_uid);
			return base_lvalue_result;
		}
		use std::convert::TryFrom;
		let result_ty = cmp_ty(&fields[field_index].1, &ctxt.structs, llvm::Ty::Void);
		let field_index: u64 = u64::try_from(field_index).expect("could not convert from usize to u64");
		let mut stream = base_lvalue_result.stream;
		let field_addr_uid = gensym("field");
		stream.push(Component::Instr(field_addr_uid.clone(), llvm::Instruction::Gep{
			typ: llvm::Ty::NamedStruct(struct_name),
			base: base_lvalue_result.llvm_op,
			offsets: vec![
				(llvm::Ty::Int{bits: 1, signed: false}, llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: 0})),
				(llvm::Ty::Int{bits: 32, signed: false}, llvm::Operand::Const(llvm::Constant::UInt{bits: 32, val: field_index}))
			]
		}));
		ExpResult{
			llvm_typ: result_ty,
			llvm_op: llvm::Operand::Local(field_addr_uid),
			stream
		}
	},
	ast::Expr::Deref(base) => {
		let mut result = cmp_exp(base as &ast::Expr, ctxt, None);
		result.llvm_typ = result.llvm_typ.remove_ptr();
		result
	},
	other => panic!("{:?} is not a valid lvalue", other)
}}

fn cmp_lvalue_to_rvalue(e: &ast::Expr, gensym_seed: &str, ctxt: &Context) -> ExpResult {
	let mut lvalue_result = cmp_lvalue(e, ctxt);
	if matches!(lvalue_result.llvm_typ, llvm::Ty::Dynamic(_)) {
		//when dealing with rvalues, if it's llvm type is Dynamic(_), then the operand is a pointer
		//to the data, not the data itself
		return lvalue_result;
	}
	let loaded_id = gensym(gensym_seed);
	//lvalue_result.llvm_typ = lvalue_result.llvm_typ.remove_ptr();
	lvalue_result.stream.push(
		Component::Instr(loaded_id.clone(), llvm::Instruction::Load{
			typ: lvalue_result.llvm_typ.clone(),
			src: lvalue_result.llvm_op
		})
	);
	//don't need to change the typ, it is already the type of the var
	lvalue_result.llvm_op = llvm::Operand::Local(loaded_id);
	lvalue_result
}

fn cmp_binary_op(bop: &ast::BinaryOp) -> llvm::BinaryOp {
	use ast::BinaryOp as SrcOp;
	use llvm::BinaryOp as LOp;
	match bop {
		SrcOp::Add => LOp::Add,
		SrcOp::Sub => LOp::Sub,
		SrcOp::Mul => LOp::Mul,
		SrcOp::Div => LOp::Div,
		SrcOp::Mod => LOp::Mod,
		SrcOp::And => LOp::And,
		SrcOp::Or => LOp::Or,
		SrcOp::Bitand => LOp::Bitand,
		SrcOp::Bitor => LOp::Bitor,
		SrcOp::Bitxor => LOp::Bitxor,
		SrcOp::Shl => LOp::Shl,
		SrcOp::Shr => LOp::Shr,
		SrcOp::Sar => LOp::Sar,
		_ => panic!("{:?} cannot be converted to an llvm BinaryOp", bop)
	}
}

fn cmp_cond_op(bop: &ast::BinaryOp) -> llvm::Cond {
	use ast::BinaryOp as SrcOp;
	use llvm::Cond as LOp;
	match bop {
		SrcOp::Equ => LOp::Equ,
		SrcOp::Neq => LOp::Neq,
		SrcOp::Gt => LOp::Gt,
		SrcOp::Gte => LOp::Gte,
		SrcOp::Lt => LOp::Lt,
		SrcOp::Lte => LOp::Lte,
		_ => panic!("{:?} cannot be converted to an llvm Cond", bop)
	}
}

fn cmp_stmt(stmt: &ast::Stmt, ctxt: &mut Context, expected_ret_ty: &llvm::Ty) -> Stream { match stmt {
	ast::Stmt::Assign(lhs, rhs) => {
		let dest_result = cmp_lvalue(lhs, ctxt);
		let mut data_result = cmp_exp(rhs, ctxt, Some(&dest_result.llvm_typ));
		#[cfg(debug_assertions)]
		if dest_result.llvm_typ != data_result.llvm_typ {
			eprintln!("dest_result.llvm_typ = {}", dest_result.llvm_typ);
			eprintln!("data_result.llvm_typ = {}", data_result.llvm_typ);
		}
		let mut stream = dest_result.stream;
		stream.append(&mut data_result.stream);
		if let llvm::Ty::Dynamic(dst) = data_result.llvm_typ {
			let ExpResult{llvm_op: sizeof_op, stream: mut sizeof_stream, ..} = cmp_exp(&ast::Expr::Sizeof(dst), ctxt, None);
			stream.append(&mut sizeof_stream);
			//memcpy(dest_result.llvm_op, data_result.llvm_op, sizeof_result.llvm_op);
			let i8_ptr: llvm::Ty = llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}));
			stream.push(Component::Instr(String::new(), llvm::Instruction::Call{
				func_name: LLVM_MEMCPY_FUNC_NAME.to_owned(),
				ret_typ: llvm::Ty::Void,
				args: vec![
					(i8_ptr.clone(), dest_result.llvm_op),
					(i8_ptr, data_result.llvm_op),
					(llvm::Ty::Int{bits: 64, signed: false}, sizeof_op),
					(llvm::Ty::Int{bits: 1, signed: false}, llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: 0}))
				]
			}));
			
		} else {
			stream.push(Component::Instr(String::new(), llvm::Instruction::Store{
				typ: data_result.llvm_typ,
				data: data_result.llvm_op,
				dest: dest_result.llvm_op
			}));
		}
		stream
	},
	ast::Stmt::Decl(typ, var_name) => {
		let uid = gensym(format!("{}_loc", var_name).as_str());
		if typ.is_DST(ctxt.structs) {
			//this declaration requires dynamic alloca
			let llvm_typ = llvm::Ty::Dynamic(typ.clone());
			ctxt.locals.insert(var_name.clone(), (llvm_typ, llvm::Operand::Local(uid.clone())));
			let mut sizeof_result = cmp_exp(&ast::Expr::Sizeof(typ.clone()), ctxt, None);
			sizeof_result.stream.push(Component::Instr(uid, llvm::Instruction::Alloca(
				llvm::Ty::Int{bits: 8, signed: false}, sizeof_result.llvm_op, Some(8)
			)));
			sizeof_result.stream
		} else {
			//even if the type is not dynamically sized, it could be a pointer to a DST,
			//and cmp_ty will yield a Ptr(llvm::Ty::Dynamic), so I recursively replace any Dynamics with i8
			//the Ty in the context should be the original, but the Ty in the llvm program should have
			//its Dynamics replaced with i8
			fn replace_dynamic_with_i8(t: &mut llvm::Ty) {
				match t {
					llvm::Ty::Dynamic(_) => {*t = llvm::Ty::Int{bits: 8, signed: false}},
					llvm::Ty::Ptr(boxed) => replace_dynamic_with_i8(boxed.as_mut()),
					llvm::Ty::Array{typ, ..} => if let llvm::Ty::Dynamic(_) = typ.as_ref() {
						*t = llvm::Ty::Int{bits: 8, signed: false}
					},
					_ => ()
				}
			}
			let mut llvm_typ = cmp_ty(typ, &ctxt.structs, llvm::Ty::Void);
			ctxt.locals.insert(var_name.clone(), (llvm_typ.clone(), llvm::Operand::Local(uid.clone())));
			replace_dynamic_with_i8(&mut llvm_typ);
			vec![Component::Instr(uid, llvm::Instruction::Alloca(llvm_typ, llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 1}), None))]
		}
	},
	ast::Stmt::Return(Some(expr)) => {
		let mut expr_result = cmp_exp(expr, ctxt, Some(expected_ret_ty));
		if let llvm::Ty::Dynamic(dst) = expr_result.llvm_typ {
			//there will be an llvm local that indicates where to write the result to
			let ExpResult{llvm_op: sizeof_op, stream: mut sizeof_stream, ..} = cmp_exp(&ast::Expr::Sizeof(dst), ctxt, None);
			expr_result.stream.append(&mut sizeof_stream);
			let i8_ptr = llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}));
			expr_result.stream.push(Component::Instr(String::new(), llvm::Instruction::Call{
				func_name: LLVM_MEMCPY_FUNC_NAME.to_owned(),
				ret_typ: llvm::Ty::Void,
				args: vec![
					(i8_ptr.clone(), llvm::Operand::Local(RET_LOC_NAME.to_owned())),
					(i8_ptr, expr_result.llvm_op),
					(llvm::Ty::Int{bits: 64, signed: false}, sizeof_op),
					(llvm::Ty::Int{bits: 1, signed: false}, llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: 0}))
				]
			}));
			expr_result.stream.push(Component::Term(llvm::Terminator::Ret(None)));
			expr_result.stream
		} else { //not returning a DST
			expr_result.stream.push(Component::Term(llvm::Terminator::Ret(
				Some((expr_result.llvm_typ, expr_result.llvm_op))
			)));
			expr_result.stream
		}
	},
	ast::Stmt::Return(None) => {
		vec![Component::Term(llvm::Terminator::Ret(None))]
	},
	ast::Stmt::SCall(func_name, args) => {
		let call_result = cmp_call(func_name.clone(), args, ctxt);
		//I can just ignore the operand that this produces
		call_result.stream
	},
	ast::Stmt::GenericSCall{..} => panic!("generic_scall not implemented yet"),
	ast::Stmt::If(cond, then_block, else_block) => {
		let cond_result = cmp_exp(cond, ctxt, None);
		let then_lbl = gensym("then");
		let else_lbl = gensym("else");
		let merge_lbl = gensym("merge");
		let mut then_stream = cmp_block(then_block, ctxt, expected_ret_ty);
		let mut else_stream = cmp_block(else_block, ctxt, expected_ret_ty);
		let mut stream = cond_result.stream;
		stream.reserve(then_stream.len() + else_stream.len() + 6);
		stream.push(Component::Term(llvm::Terminator::CondBr{
			condition: cond_result.llvm_op,
			true_dest: then_lbl.clone(),
			false_dest: else_lbl.clone(),
		}));
		stream.push(Component::Label(then_lbl));
		stream.append(&mut then_stream);
		stream.push(Component::Term(llvm::Terminator::Br(merge_lbl.clone())));
		stream.push(Component::Label(else_lbl));
		stream.append(&mut else_stream);
		stream.push(Component::Term(llvm::Terminator::Br(merge_lbl.clone())));
		stream.push(Component::Label(merge_lbl));
		stream
	},
	ast::Stmt::While(cond, body) => {
		let mut cond_result = cmp_exp(cond, ctxt, None);
		let check_lbl = gensym("check_cond");
		let body_lbl = gensym("body");
		let after_lbl = gensym("after");
		let mut body_stream = cmp_block(body, ctxt, expected_ret_ty);
		let mut stream = Vec::new();
		stream.reserve(cond_result.stream.len() + body_stream.len() + 6);
		stream.push(Component::Term(llvm::Terminator::Br(check_lbl.clone())));
		stream.push(Component::Label(check_lbl.clone()));
		stream.append(&mut cond_result.stream);
		stream.push(Component::Term(llvm::Terminator::CondBr{
			condition: cond_result.llvm_op,
			true_dest: body_lbl.clone(),
			false_dest: after_lbl.clone()
		}));
		stream.push(Component::Label(body_lbl));
		stream.append(&mut body_stream);
		stream.push(Component::Term(llvm::Terminator::Br(check_lbl)));
		stream.push(Component::Label(after_lbl));
		stream
	}
}}

fn cmp_block(block: &[ast::Stmt], ctxt: &mut Context, expected_ret_ty: &llvm::Ty) -> Stream {
	let mut stream = Vec::new();
	for stmt in block.iter() {
		stream.append(&mut cmp_stmt(stmt, ctxt, expected_ret_ty));
	}
	//if the function returns void, a return statement can be elided. In this case, the stream
	//will not end with a terminator, and a 'ret void' terminator should be added
	if stream.is_empty() || !matches!(stream.last().unwrap(), Component::Term(_)) {
		stream.push(Component::Term(llvm::Terminator::Ret(None)));
	}
	stream
}

fn mangle_type(t: &ast::Ty, output: &mut String) {
	use ast::Ty::*;
	use std::fmt::Write;
	//if it ends in ., it's a pointer
	//if it ends in .123, it's an array
	//if it ends in .struct, it's a struct
	match t {
		Bool | Int{..} | Float(_) => write!(output, "{}", t).unwrap(),
		Ptr(None) => output.push_str("void."),
		Ptr(Some(boxed)) => {
			write!(output, "{}", boxed as &ast::Ty).unwrap();
			output.push('.');
		},
		Array{length, typ: boxed} => write!(output, "{}.{}", boxed as &ast::Ty, length).unwrap(),
		Struct(s) => write!(output, "{}.struct", s).unwrap(),
		TypeVar(s) => panic!("Cannot mangle a TypeVar {}", s),
		GenericStruct{type_var, name} => panic!("Cannot mangle a generic struct with type param {} and name {}", type_var, name)
	}
}

//functions and type defs can have the same name, so only one mangling function is needed
fn mangle(name: &str, ty: &ast::Ty) -> String {
	let mut result_string = name.to_owned();
	result_string.push('$');
	mangle_type(ty, &mut result_string);
	result_string
}

#[allow(dead_code)]
enum FuncInst<'a, 'b>{
	NonGeneric(&'a ast::Func),
	Erased(&'a ast::GenericFunc),
	Separated(&'a ast::GenericFunc, &'b ast::Ty)
}
fn cmp_func(f: &FuncInst, prog_context: &typechecker::ProgramContext, global_locs: &HashMap<String, (llvm::Ty, llvm::Operand)>) -> (llvm::Func, Vec<(String, llvm::GlobalDecl)>) {
	//compiling a non-generic function and an erased function are nearly the same thing
	let mut context = Context{
		locals: HashMap::new(),
		globals: global_locs,
		funcs: &prog_context.funcs,
		structs: &prog_context.structs,
		mode: None
	};
	let (args, ret_ty, func_name, body) = match f {
		FuncInst::NonGeneric(f) => (&f.args, &f.ret_type, &f.name as &str, &f.body),
		FuncInst::Erased(_) => {context.mode = Some(ast::PolymorphMode::Erased); todo!()},
		FuncInst::Separated(_,_) => {context.mode = Some(ast::PolymorphMode::Separated); todo!()}
	};
	let mut stream = Vec::with_capacity(args.len() * 2);
	let mut params = Vec::with_capacity(args.len());
	let (ret_is_dst, ll_ret_ty) = match ret_ty {
		None => (false, llvm::Ty::Void),
		Some(t) if t.is_DST(&prog_context.structs) => (true, llvm::Ty::Void),
		Some(t) => (false, cmp_ty(t, &prog_context.structs, llvm::Ty::Void))
	};
	for (arg_ty, arg_name) in args.iter() {
		let alloca_slot_id = gensym("arg_slot");
		let ll_ty = cmp_ty(arg_ty, &prog_context.structs, llvm::Ty::Void);
		let ll_arg_id = gensym("arg");
		stream.push(Component::Instr(alloca_slot_id.clone(), llvm::Instruction::Alloca(ll_ty.clone(), llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 1}), None)));
		stream.push(Component::Instr(String::new(), llvm::Instruction::Store{
			typ: ll_ty.clone(),
			data: llvm::Operand::Local(ll_arg_id.clone()),
			dest: llvm::Operand::Local(alloca_slot_id.clone())
		}));
		context.locals.insert(arg_name.clone(), (ll_ty.clone(), llvm::Operand::Local(alloca_slot_id)));
		params.push( (ll_ty, ll_arg_id) );
	}
	if ret_is_dst {
		//the DST return location does not get moved from a local to a stack slot because it will never
		//be modified like normal function parameters. It also is not added to the context.
		params.push( (llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})), RET_LOC_NAME.to_owned()) );
	}
	let body_stream = cmp_block(body, &mut context, &ll_ret_ty);
	//convert stream + body_stream to CFG
	let mut cfg = llvm::CFG{
		entry: Default::default(),
		other_blocks: Vec::new()
	};
	//let mut current_block: Option<(&str, llvm::Block)> = Some("", Vec::new());
	//if GlobalString(ident, GString("abc")) appears in the stream,
	//the Program.global_decls needs to have (ident, GString("abc") appended to it.
	let mut additional_gdecls = Vec::new();
	let mut seen_first_term = false;
	for component in stream.into_iter().chain(body_stream.into_iter()) { match component {
		Component::Label(s) => {
			debug_assert!(seen_first_term, "entry block of function {} does not have a terminator", func_name);
			cfg.other_blocks.push( (s, Default::default()) );
		},
		Component::Instr(dest, insn) => {
			if seen_first_term {
				let (_, current_block): &mut (_, llvm::Block) = cfg.other_blocks.last_mut().expect("instruction after terminator, but without label before it");
				current_block.insns.push( (dest, insn) );
			} else {
				cfg.entry.insns.push( (dest, insn) );
			}
		},
		Component::Term(term) => {
			if seen_first_term {
				let (_, current_block) = cfg.other_blocks.last_mut().expect("terminator without label");
				current_block.term = term;
			} else {
				cfg.entry.term = term;
				seen_first_term = true;
			}
		},
		Component::GlobalString(ident, decl) => {
			additional_gdecls.push( (ident, decl) );
		}
	}}

	let possibly_mangled_name: String = match f {
		FuncInst::NonGeneric(_) | FuncInst::Erased(_) => func_name.to_owned(),
		FuncInst::Separated(_, ty) => mangle(func_name, ty)
	};
	let func_result = llvm::Func{
		ret_ty: ll_ret_ty,
		params,
		cfg,
		name: possibly_mangled_name
	};
	(func_result, additional_gdecls)
}

type LLStructContext = HashMap<String, Vec<llvm::Ty>>;

fn get_default_constant(ll_ty: &llvm::Ty, structs: &LLStructContext) -> llvm::Constant {
	use llvm::Ty::*;
	match ll_ty {
		Int{..} => llvm::Constant::SInt{bits: 0, val: 0},
		Float32 | Float64 => llvm::Constant::Float64(0.0),
		Ptr(_) => llvm::Constant::Null(llvm::Ty::Void),
		Array{length, typ} => llvm::Constant::Array{
			typ: (typ as &llvm::Ty).clone(),
			elements: std::iter::once(get_default_constant(typ, structs)).cycle().take(*length).collect()
		},
		NamedStruct(s) => llvm::Constant::Struct{
			name: s.clone(),
			values: structs.get(s).expect("types of global vars should be insted by now")
				.iter()
				.map(|t| get_default_constant(t, structs))
				.collect()
		},
		Void => panic!("global cannot have void type"),
		Dynamic(t) => panic!("global vars cannot be dynamically sized, like {}", t),
	}
}

fn cmp_global_var(typ: &ast::Ty, structs: &typechecker::StructContext, ll_structs: &LLStructContext) -> (llvm::Ty, llvm::GlobalDecl) {
	let ll_ty = cmp_ty(typ, structs, llvm::Ty::Void);
	let initializer: llvm::Constant = get_default_constant(&ll_ty, ll_structs);
	(ll_ty.clone(), llvm::GlobalDecl::GConst(ll_ty, initializer))
}

//when insting this, replace all occurences of its type var in fields with type_param
#[allow(dead_code)]
struct StructInst<'prog>{
	name: &'prog str,
	type_param: &'prog ast::Ty
}

#[derive(Default)]
struct InstQueue<'prog>{
	queue: VecDeque<StructInst<'prog>>,
	already_insted: HashSet<(&'prog str, &'prog ast::Ty)>
}
impl<'s, 'prog> InstQueue<'prog>{
	fn push(&'s mut self, struct_name: &'prog str, type_param: &'prog ast::Ty) -> bool {
		if self.already_insted.contains(&(struct_name, type_param)){
			false
		} else {
			self.queue.push_back(StructInst{
				name: struct_name,
				type_param
			});
			self.already_insted.insert((struct_name, type_param));
			true
		}
	}
	#[allow(dead_code)]
	fn poll(&'s mut self) -> Option<StructInst<'prog>>{
		self.queue.pop_front()
	}
}

pub fn cmp_prog<'prog>(prog: &'prog ast::Program, prog_context: &'prog typechecker::ProgramContext) -> llvm::Program {
	let mut type_decls: LLStructContext = HashMap::new();
	let mut struct_inst_queue: InstQueue<'prog> = Default::default();
	//initially, put all non-generic and erased structs in the type_decls
	for s in prog.structs.iter() {
		//any structs that are dynamically sized do not get declared, llvm does not know about them
		if s.fields.iter().any(|(t, _)| t.is_DST(&prog_context.structs)) {continue}
		let cmped_tys = s.fields.iter().map(|(t, _)| cmp_ty(t, &prog_context.structs, llvm::Ty::Void)).collect();
		type_decls.insert(s.name.clone(), cmped_tys);
	}
	//erased structs do not get declared, llvm does not know about them
	//they don't need to be in `type_decls`, because globals vars cannot be DSTs

	let mut global_decls: Vec<(String, llvm::GlobalDecl)> = Vec::with_capacity(prog.global_vars.len());
	let mut global_locs: HashMap<String, (llvm::Ty, llvm::Operand)> = HashMap::new();
	for (typ, name) in prog.global_vars.iter() {
		//if typ is a struct name@<type_param>
		if let ast::Ty::GenericStruct{type_var: type_param, name} = typ {
			//..and struct name is declared as a struct using struct name@<separated 'type_var>{...}
			if let typechecker::StructType::Generic{mode: ast::PolymorphMode::Separated, ..} = prog_context.structs.get(name).unwrap() {
				struct_inst_queue.push(name, type_param);
			}
		}
		let (ll_typ, ll_gdecl) = cmp_global_var(typ, &prog_context.structs, &type_decls);
		global_decls.push( (name.clone(), ll_gdecl) );
		global_locs.insert(name.clone(), (ll_typ, llvm::Operand::Global(name.clone())));
	}
	let mut cmped_funcs = Vec::new();
	for func in prog.funcs.iter() {
		let (func, extra_globals) = cmp_func(&FuncInst::NonGeneric(func), prog_context, &global_locs);
		cmped_funcs.push(func);
		global_decls.extend(extra_globals.into_iter());
	}
	llvm::Program {
		type_decls,
		global_decls,
		func_decls: cmped_funcs,
		external_decls: vec![
				("malloc".to_owned(),
				llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
				vec![llvm::Ty::Int{bits: 64, signed: false}]),

				("free".to_owned(),
				llvm::Ty::Void,
				vec![llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))]
				)
			]
	}
}
