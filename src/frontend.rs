use crate::ast2;
use crate::typechecker;
use crate::typechecker::PRINTF_FAMILY;
use crate::llvm;
use std::collections::{HashSet, HashMap, VecDeque};
use std::sync::Mutex;
use rayon::prelude::*;

pub struct Context<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>{
	locals: HashMap<String, (llvm::Ty<'src, 'arena>, llvm::Operand<'src, 'arena>)>,
	globals: &'front HashMap<String, (llvm::Ty<'src, 'arena>, llvm::Operand<'src, 'arena>)>,
	funcs: &'arena typechecker::FuncContext<'src, 'arena>,
	structs: &'arena typechecker::StructContext<'src, 'arena>,
	mode: Option<ast2::PolymorphMode>,
	struct_inst_queue: &'front Mutex<SeparatedStructInstQueue<'src, 'arena>>,
	func_inst_queue: &'front Mutex<SeparatedFuncInstQueue<'src, 'arena>>,
	current_separated_type_param: Option<(&'arena ast2::Ty<'src, 'arena>, llvm::Ty<'src, 'arena>)>,
	current_separated_func_depth: u8,
	errno_func_name: &'arena str,
	stream: Stream<'src, 'arena>,
	typecache: &'arena ast2::TypeCache<'src, 'arena>,
	_must_use_func_placeholder: &'func std::marker::PhantomData<()>,
}
impl<'src: 'arena, 'arena: 'front, 'front: 'func, 'func> Context<'src, 'arena, 'front, 'func> {
	fn get_var(&self, name: &str) -> &(llvm::Ty<'src, 'arena>, llvm::Operand<'src, 'arena>) {
		self.locals.get(name)
			.or_else(|| self.globals.get(name))
			.unwrap_or_else(|| panic!("why is variable {} not in the context", name))
	}
	#[allow(dead_code)]
	fn type_param_or_void(&self) -> llvm::Ty<'src, 'arena> {
		match &self.current_separated_type_param {
			None => llvm::Ty::Void,
			Some((_, t)) => t.clone()
		}
	}
	fn current_src_type_param(&self) -> Option<&'arena ast2::Ty<'src, 'arena>> {
		match &self.current_separated_type_param {
			None => None,
			Some((t, _)) => Some(t)
		}
	}
}

#[allow(clippy::large_enum_variant)]
pub enum Component<'src: 'arena, 'arena>{
	Label(String),														//label of a block
	Instr(String, llvm::Instruction<'src, 'arena>),						//regular instruction
	Term(llvm::Terminator<'src, 'arena>),								//terminator of a block
	GlobalString(String, llvm::GlobalDecl<'src, 'arena>),				//string that needs to be moved to global scope
	//Alloca'd memory is valid for the entire function, so moving them to the entry block is useless
		//unless I need the location of a variable before I Alloca it?
	//Entry(String, llvm::Instruction),									//instruction that needs to be moved to the entry block (usually an Alloca Instruction)
}
impl<'src: 'arena, 'arena> std::fmt::Debug for Component<'src, 'arena>{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Component::*;
		match self {
			Label(s) => writeln!(f, "label '{}'", s),
			Instr(dest, instr) => writeln!(f, "instr %{} = {}", dest, instr),
			Term(t) => writeln!(f, "term {}", t),
			GlobalString(s, gdecl) => writeln!(f, "GlobalString '{}', {}", s, gdecl)
		}
	}
}

pub type Stream<'src, 'arena> = Vec<Component<'src, 'arena>>;

pub fn gensym(s: &str) -> String {
	use std::sync::atomic::{AtomicUsize, Ordering};
	static GENSYM_COUNT: AtomicUsize = AtomicUsize::new(0);
	let n_copy: usize = GENSYM_COUNT.fetch_add(1, Ordering::Relaxed);
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
fn cmp_ty<'src: 'arena, 'arena>(
		t: &'arena ast2::Ty<'src, 'arena>,
		structs: &typechecker::StructContext<'src, 'arena>,
		type_var_replacement: Option<&'arena ast2::Ty<'src, 'arena>>,
		mode: Option<ast2::PolymorphMode>,
		struct_inst_queue: &Mutex<SeparatedStructInstQueue<'src, 'arena>>,
		typecache: &'arena ast2::TypeCache<'src, 'arena>
		) -> llvm::Ty<'src, 'arena> {
	if t.is_DST(structs, mode, typecache) {
		return llvm::Ty::Dynamic(t);
	}
	match t {
		ast2::Ty::Bool => llvm::Ty::Int{bits: 1, signed: false},
		ast2::Ty::Int{size: ast2::IntSize::Size8, signed} => llvm::Ty::Int{bits: 8, signed: *signed},
		ast2::Ty::Int{size: ast2::IntSize::Size16, signed} => llvm::Ty::Int{bits: 16, signed: *signed},
		ast2::Ty::Int{size: ast2::IntSize::Size32, signed} => llvm::Ty::Int{bits: 32, signed: *signed},
		ast2::Ty::Int{size: ast2::IntSize::Size64, signed} => llvm::Ty::Int{bits: 64, signed: *signed},
		ast2::Ty::Float(ast2::FloatSize::FSize32) => llvm::Ty::Float32,
		ast2::Ty::Float(ast2::FloatSize::FSize64) => llvm::Ty::Float64,
		ast2::Ty::Ptr(None) => llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
		ast2::Ty::Ptr(Some(t1)) => llvm::Ty::Ptr(Box::new(cmp_ty(t1, structs, type_var_replacement, mode, struct_inst_queue, typecache))),
		ast2::Ty::Array{length, typ} => llvm::Ty::Array{length: *length as usize, typ: Box::new(cmp_ty(typ, structs, type_var_replacement, mode, struct_inst_queue, typecache))},
		ast2::Ty::Struct(s) => llvm::Ty::NamedStruct(s.to_string(), s.to_string(), None),
		ast2::Ty::GenericStruct{type_param, name} => {
			match structs.get(name) {
				Some(typechecker::StructType::Generic{mode: ast2::PolymorphMode::Erased, ..}) =>
					//already checked for is_DST above
					unreachable!(),
				Some(typechecker::StructType::Generic{mode: ast2::PolymorphMode::Separated, ..}) => {
					let mut possibly_replaced_type_param: &ast2::Ty<'_, '_> = type_param;
					match type_var_replacement {
						None => debug_assert!(type_param.recursively_find_type_var().is_none(), "cmp_ty called on generic struct with a type param that is not completely concrete, {:?}, and current_separated_type_param is None", t),
						Some(replacement) => {
							possibly_replaced_type_param = possibly_replaced_type_param.replace_type_var_with(replacement, typecache)
						}
					};
					struct_inst_queue.lock().unwrap().push(name.to_string(), possibly_replaced_type_param);
					//call cmp_ty on the type param, but do nothing with it, just to add it to the struct inst queue in case it is a separated struct
					cmp_ty(type_param, structs, type_var_replacement, mode, struct_inst_queue, typecache);
					llvm::Ty::NamedStruct(mangle(name, possibly_replaced_type_param), name.to_string(), Some(possibly_replaced_type_param))
				}
				None => panic!("could not find {} in struct context", name),
				Some(typechecker::StructType::NonGeneric(_)) => panic!("struct {} is not generic", name),
			}
		},
		ast2::Ty::TypeVar(s) => {
			debug_assert!(*s != "_should_not_happen", "TypeVar is _should_not_happen");
			cmp_ty(type_var_replacement.unwrap(), structs, None, mode, struct_inst_queue, typecache)
		}
	}
}

pub struct ExpResult<'src: 'arena, 'arena>{
	pub llvm_typ: llvm::Ty<'src, 'arena>,
	//If llvm_typ is not Dynamic(_), then llvm_op has that type
	//if llvm_typ is Dynamic(_), then llvm_op is an i8*
	pub llvm_op: llvm::Operand<'src, 'arena>,
}
impl<'src: 'arena, 'arena> std::fmt::Debug for ExpResult<'src, 'arena> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		writeln!(f, "llvm_typ: {:?}", self.llvm_typ)?;
		writeln!(f, "llvm_op: {}", self.llvm_op)?;
		Ok(())
	}
}

fn cmp_exp<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>(
		e: &'arena ast2::TypedExpr<'src, 'arena>,
		ctxt: &mut Context<'src, 'arena, 'front, 'func>
		) -> ExpResult<'src, 'arena> { match &e.expr {
	ast2::Expr::LitNull => {
		let llvm_typ = cmp_ty(e.typ.unwrap(), ctxt.structs, ctxt.current_separated_type_param.as_ref().map(|pair| pair.0), ctxt.mode, ctxt.struct_inst_queue, ctxt.typecache);
		ExpResult {
			llvm_typ: llvm_typ.clone(),
			llvm_op: llvm::Operand::Const(llvm::Constant::Null(llvm_typ)),
		}
	},
	ast2::Expr::LitBool(b) => ExpResult{
		llvm_typ: llvm::Ty::Int{bits: 1, signed: false},
		llvm_op: llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: if *b {1} else {0} }),
	},
	ast2::Expr::LitSignedInt(i, size) => ExpResult{
		llvm_typ: llvm::Ty::Int{bits: 64, signed: true},
		llvm_op: llvm::Operand::Const(llvm::Constant::SInt{bits: size.num_bits().into(), val: *i}),
	},
	ast2::Expr::LitUnsignedInt(i, size) => ExpResult{
		llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
		llvm_op: llvm::Operand::Const(llvm::Constant::UInt{bits: size.num_bits().into(), val: *i}),
	},
	ast2::Expr::LitFloat(f, ast2::FloatSize::FSize32) => ExpResult{
		llvm_typ: llvm::Ty::Float32,
		llvm_op: llvm::Operand::Const(llvm::Constant::Float32(*f)),
	},
	ast2::Expr::LitFloat(f, ast2::FloatSize::FSize64) => ExpResult{
		llvm_typ: llvm::Ty::Float64,
		llvm_op: llvm::Operand::Const(llvm::Constant::Float64(*f)),
	},
	ast2::Expr::LitString(s) => {
		let global_string_ident = gensym("string_literal_array");
		let casted_local_ident = gensym("string_pointer");
		let global_typ = llvm::Ty::Array{
			length: s.len()+1,
			typ: Box::new(llvm::Ty::Int{bits: 8, signed: false})
		};
		ctxt.stream.push(Component::GlobalString(global_string_ident.to_string(), llvm::GlobalDecl::GString(s.to_string())));
		ctxt.stream.push(Component::Instr(casted_local_ident.clone(), llvm::Instruction::Bitcast{
			original_typ: llvm::Ty::Ptr(Box::new(global_typ)),
			new_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
			op: llvm::Operand::Global(global_string_ident)
		}));
		ExpResult{
			llvm_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
			llvm_op: llvm::Operand::Local(casted_local_ident),
		}
	},
	ast2::Expr::Id(s) => cmp_lvalue_to_rvalue(e, &format!("{}_loaded", s) as &str, ctxt),
	ast2::Expr::Deref(_) => cmp_lvalue_to_rvalue(e, "deref_loaded", ctxt),
	//llvm doesn't allow me to use extractvalue on an array (unless I know the idnex at compile time),
	//so I have to use getelementptr, and can't have arrays that aren't lvalues

	ast2::Expr::Index(_,_) => cmp_lvalue_to_rvalue(e, "index_loaded", ctxt),
	//I added code here (rvalue Proj) to to handle dynamic structs. I may have to do a similar thing for rvalue Index,
	//but for now it seems to be working
	ast2::Expr::Proj(base, field_name) => {
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
		let mut base_result = cmp_exp(base, ctxt);
		//The cases for Dynamic(Struct(s)) and Ptr(Dynamic(Struct(s))) are the same thing
		let mut base_type_param: Option<&'arena ast2::Ty<'_, '_>> = None;
		let (is_dynamic, base_is_ptr, struct_name) = match &base_result.llvm_typ {
			llvm::Ty::Dynamic(ast2::Ty::Struct(s)) => (true, true, s.to_string()),
			llvm::Ty::Dynamic(ast2::Ty::GenericStruct{name: s, type_param}) => {
				base_type_param = Some(type_param);
				(true, true, s.to_string())
			},
			llvm::Ty::NamedStruct(_llvm_name, src_name, type_param) => {
				base_type_param = *type_param;
				(false, false, src_name.to_string())
			},
			llvm::Ty::Ptr(boxed) => match boxed as &llvm::Ty {
				llvm::Ty::Dynamic(ast2::Ty::Struct(s)) => (true, true, s.to_string()),
				llvm::Ty::Dynamic(ast2::Ty::GenericStruct{name: s, type_param}) => {
					base_type_param = Some(type_param);
					(true, true, s.to_string())
				},
				llvm::Ty::NamedStruct(_llvm_name, src_name, type_param) => {
					base_type_param = *type_param;
					(false, true, src_name.clone())
				},
				t => panic!("Proj base has llvm type Ptr({:?})", t)
			},
			t => panic!("Proj base has llvm type {:?}", t)
		};
		let fields: &[(_, &ast2::Ty<'_, '_>)] = match ctxt.structs.get(struct_name.as_str()) {
			None => panic!("struct {} not in struct_context", &struct_name),
			Some(typechecker::StructType::NonGeneric(fields)) => fields,
			Some(typechecker::StructType::Generic{fields, ..}) => fields
		};
		let mut field_index: Option<usize> = None;
		for (i, (name, _src_ty)) in fields.iter().enumerate() {
			if name == &field_name.elt {
				field_index = Some(i);
				break;
			}
		}
		let field_index: usize = field_index.unwrap_or_else(|| panic!("field name {} not found in struct {}", field_name, struct_name));
		if is_dynamic {
			let preceding_fields_iter = fields.iter().take(field_index).map(|(_, t)| *t);
			let base_type_param = base_type_param.unwrap_or_else(|| ast2::Ty::TypeVar("_should_not_happen").getref(ctxt.typecache));
			let offset_op = cmp_size_of_erased_struct(preceding_fields_iter, ctxt, base_type_param);
			let ptr_offset_op = gensym("DST_offset");
			ctxt.stream.push(Component::Instr(ptr_offset_op.clone(), llvm::Instruction::Gep{
				typ: llvm::Ty::Int{bits: 8, signed: false},
				base: base_result.llvm_op,
				offsets: vec![(llvm::Ty::Int{bits: 64, signed: false}, offset_op)]
			}));
			let field_typ: &ast2::Ty<'_, '_> = fields[field_index].1.replace_type_var_with(base_type_param, ctxt.typecache);
			if !field_typ.is_DST(ctxt.structs, ctxt.mode, ctxt.typecache) {
				//only load from it if it is not a dynamic type
				//first, bitcast the i8* to the right type
				let llvm_field_typ = cmp_ty(field_typ, ctxt.structs, 
					//if the base type is a regular struct that is dynamic, then don't need to pass
					//a replacement type here, otherwise the type parameter must be cmped
					Some(base_type_param),
					ctxt.mode,
					ctxt.struct_inst_queue,
					ctxt.typecache
				);
				let bitcasted_uid = gensym("proj_bitcast");
				ctxt.stream.push(Component::Instr(bitcasted_uid.clone(), llvm::Instruction::Bitcast{
					original_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
					op: llvm::Operand::Local(ptr_offset_op),
					new_typ: llvm::Ty::Ptr(Box::new(llvm_field_typ.clone()))
				}));
				let loaded_uid = gensym("proj_load");
				ctxt.stream.push(Component::Instr(loaded_uid.clone(), llvm::Instruction::Load{
					typ: llvm_field_typ.clone(),
					src: llvm::Operand::Local(bitcasted_uid)
				}));
				return ExpResult{
					llvm_typ: llvm_field_typ,
					llvm_op: llvm::Operand::Local(loaded_uid),
				}
			}
			//if the result is dynamic, it is already an i8*, so nothing needs to be done
			return ExpResult{
				llvm_typ: llvm::Ty::Dynamic(field_typ),
				llvm_op: llvm::Operand::Local(ptr_offset_op),
			}
		}
		use std::convert::TryFrom;
		let result_ty = cmp_ty(fields[field_index].1, ctxt.structs, base_type_param, ctxt.mode, ctxt.struct_inst_queue, ctxt.typecache);
		let field_index: u64 = u64::try_from(field_index).expect("could not convert from usize to u64");
		let base_loaded_op: llvm::Operand;
		if base_is_ptr {
			base_result.llvm_typ = base_result.llvm_typ.remove_ptr();
			let base_loaded_uid = gensym("base_loaded");
			base_loaded_op = llvm::Operand::Local(base_loaded_uid.clone());
			ctxt.stream.push(Component::Instr(base_loaded_uid, llvm::Instruction::Load{
				typ: base_result.llvm_typ.clone(),
				src: base_result.llvm_op
			}));
		} else {
			base_loaded_op = base_result.llvm_op;
		}
		let extracted_uid = gensym("extract");
		ctxt.stream.push(Component::Instr(extracted_uid.clone(), llvm::Instruction::Extract{
			typ: base_result.llvm_typ,
			base: base_loaded_op,
			offset: field_index
		}));
		ExpResult{
			llvm_typ: result_ty,
			llvm_op: llvm::Operand::Local(extracted_uid),
		}
	},
	ast2::Expr::Cast(new_type, src) => {
		let mut src_result = cmp_exp(src, ctxt);
		let new_type: &'arena ast2::Ty<'src, 'arena> = new_type;
		let new_llvm_typ = cmp_ty(new_type, ctxt.structs, ctxt.current_src_type_param(), ctxt.mode, ctxt.struct_inst_queue, ctxt.typecache);
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
					ctxt.stream.push(Component::Instr(truncated_uid.clone(), llvm::Instruction::Trunc{
						old_bits: *old_bits,
						op: src_result.llvm_op,
						new_bits: *new_bits,
					}));
					ExpResult{
						llvm_typ: new_llvm_typ,
						llvm_op: llvm::Operand::Local(truncated_uid),
					}
				} else {
					let extended_uid = gensym("extended");
					ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
						old_bits: *old_bits,
						op: src_result.llvm_op,
						new_bits: *new_bits,
						signed: *old_signed
					}));
					ExpResult{
						llvm_typ: new_llvm_typ,
						llvm_op: llvm::Operand::Local(extended_uid),
					}
				}
			},
			(Float32, Float32) | (Float64, Float64) => src_result,
			(Float32, Float64) => {
				let truncated_uid = gensym("float_truncated");
				ctxt.stream.push(Component::Instr(truncated_uid.clone(), 
					llvm::Instruction::FloatTrunc(src_result.llvm_op)
				));
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(truncated_uid),
				}
			},
			(Float64, Float32) => {
				let extended_uid = gensym("float_extended");
				ctxt.stream.push(Component::Instr(extended_uid.clone(), 
					llvm::Instruction::FloatExt(src_result.llvm_op)
				));
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(extended_uid),
				}
			},
			(Float32, Int{bits, signed}) | (Float64, Int{bits, signed}) => {
				let converted_uid = gensym("int_to_float");
				if *signed {
					ctxt.stream.push(Component::Instr(converted_uid.clone(), llvm::Instruction::SignedToFloat{
						old_bits: *bits,
						op: src_result.llvm_op,
						result_is_64_bit: matches!(new_llvm_typ, Float64)
					}));
				} else {
					ctxt.stream.push(Component::Instr(converted_uid.clone(), llvm::Instruction::UnsignedToFloat{
						old_bits: *bits,
						op: src_result.llvm_op,
						result_is_64_bit: matches!(new_llvm_typ, Float64)
					}));
				}
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(converted_uid),
				}
			},
			(Int{bits, signed}, Float32) | (Int{bits, signed}, Float64) => {
				let converted_uid = gensym("float_to_int");
				if *signed {
					ctxt.stream.push(Component::Instr(converted_uid.clone(), llvm::Instruction::FloatToSigned{
						new_bits: *bits,
						op: src_result.llvm_op,
						src_is_64_bit: matches!(new_llvm_typ, Float64)
					}));
				} else {
					ctxt.stream.push(Component::Instr(converted_uid.clone(), llvm::Instruction::FloatToUnsigned{
						new_bits: *bits,
						op: src_result.llvm_op,
						src_is_64_bit: matches!(new_llvm_typ, Float64)
					}));
				}
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(converted_uid),
				}
			},
			(Ptr(_), Ptr(_)) => {
				let casted_uid = gensym("ptr_cast");
				ctxt.stream.push(Component::Instr(casted_uid.clone(), llvm::Instruction::Bitcast{
					original_typ: src_result.llvm_typ,
					op: src_result.llvm_op,
					new_typ: new_llvm_typ.clone()
				}));
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(casted_uid),
				}
			}
			(new, old) => panic!("trying to cast from {:?} to {:?}", old, new)
		}
	},
	ast2::Expr::Binop(left, bop, right) => {
		if matches!(bop, And | Or) {
			//handle short-circuiting specially
			/* And case
			//No phi nodes, so I need to use memory for this
			%left_op = ...
			%and_result_loc = alloca i1
			br i1 %left_op, label %check_right_op, label %short_circuit
			short_circuit:
			store i1 0, i1* %and_result_loc
			br label %and_join
			check_right_op:
			%right_op = ...
			store i1 %right_op, i1* %and_result_loc
			br label %and_join
			and_join:
			%result = load i1, i1* %and_result_loc
			*/
			let ExpResult{llvm_op: left_op, ..} = cmp_exp(left, ctxt);
			let result_loc = gensym("short_circuit_result_loc");
			let check_right_op_lbl = gensym("check_righ_op");
			let sc_lbl = gensym("short_circuit");
			let join_lbl = gensym("short_circuit_join");
			ctxt.stream.push(Component::Instr(result_loc.clone(), llvm::Instruction::Alloca(
				llvm::Ty::Int{bits: 1, signed: false},
				llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 1}), None
			)));
			ctxt.stream.push(Component::Term(llvm::Terminator::CondBr{
				condition: left_op,
				true_dest: if *bop == And {check_right_op_lbl.clone()} else {sc_lbl.clone()},
				false_dest: if *bop == And {sc_lbl.clone()} else {check_right_op_lbl.clone()}
			}));
			ctxt.stream.push(Component::Label(sc_lbl));
			ctxt.stream.push(Component::Instr(String::new(), llvm::Instruction::Store{
				typ: llvm::Ty::Int{bits: 1, signed: false},
				data: llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: (*bop == Or) as u64}),
				dest: llvm::Operand::Local(result_loc.clone())
			}));
			ctxt.stream.push(Component::Term(llvm::Terminator::Br(join_lbl.clone())));
			ctxt.stream.push(Component::Label(check_right_op_lbl));
			let ExpResult{llvm_op: right_op, ..} = cmp_exp(right, ctxt);
			ctxt.stream.push(Component::Instr(String::new(), llvm::Instruction::Store{
				typ: llvm::Ty::Int{bits: 1, signed: false},
				data: right_op,
				dest: llvm::Operand::Local(result_loc.clone())
			}));
			ctxt.stream.push(Component::Term(llvm::Terminator::Br(join_lbl.clone())));
			ctxt.stream.push(Component::Label(join_lbl));
			let result_op = gensym("short_circuit_result");
			ctxt.stream.push(Component::Instr(result_op.clone(), llvm::Instruction::Load{
				typ: llvm::Ty::Int{bits: 1, signed: false},
				src: llvm::Operand::Local(result_loc)
			}));
			return ExpResult{
				llvm_op: llvm::Operand::Local(result_op),
				llvm_typ: llvm::Ty::Int{bits: 1, signed: false}
			}
		}
		let left_result = cmp_exp(left, ctxt);
		let right_result = cmp_exp(right, ctxt);
		use ast2::BinaryOp::*;
		match (bop, &left_result.llvm_typ, &right_result.llvm_typ) {
			//Arithmetic between Ints
			(_, llvm::Ty::Int{bits: l_bits, signed: l_signed}, llvm::Ty::Int{bits: r_bits, signed: r_signed})
					if matches!(bop, Add | Sub | Mul | Div | Mod | Bitand | Bitor | Bitxor | Shl | Shr | Sar)=> {
				let uid = gensym("int_arith");
				let mut extended_left_op = left_result.llvm_op;
				let mut extended_right_op = right_result.llvm_op;
				use std::cmp::Ordering;
				match l_bits.cmp(r_bits) {
					Ordering::Less => {
						let extended_uid = gensym("extend_for_binop");
						ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
							old_bits: *l_bits,
							op: extended_left_op,
							new_bits: *r_bits,
							signed: *l_signed
						}));
						extended_left_op = llvm::Operand::Local(extended_uid);
					},
					Ordering::Greater => {
						let extended_uid = gensym("extend_for_binop");
						ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
							old_bits: *r_bits,
							op: extended_right_op,
							new_bits: *l_bits,
							signed: *r_signed
						}));
						extended_right_op = llvm::Operand::Local(extended_uid);
					},
					Ordering::Equal => ()
				};
				ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
					op: cmp_binary_op(*bop),
					typ: llvm::Ty::Int{bits: std::cmp::max(*l_bits, *r_bits), signed: false},
					left: extended_left_op,
					right: extended_right_op
				}));
				ExpResult{
					llvm_typ: left_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
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
						ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
							old_bits: *l_bits,
							op: extended_left_op,
							new_bits: *r_bits,
							signed: *signed
						}));
						extended_left_op = llvm::Operand::Local(extended_uid);
					},
					Ordering::Greater => {
						let extended_uid = gensym("extend_for_binop");
						ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
							old_bits: *r_bits,
							op: extended_right_op,
							new_bits: *l_bits,
							signed: *signed
						}));
						extended_right_op = llvm::Operand::Local(extended_uid);
					},
					Ordering::Equal => ()
				};
				ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
					cond: cmp_cond_op(*cond_op),
					typ: llvm::Ty::Int{bits: std::cmp::max(*l_bits, *r_bits), signed: *signed},
					left: extended_left_op,
					right: extended_right_op
				}));
				ExpResult{
					llvm_typ: llvm::Ty::Int{bits: 1, signed: false},
					llvm_op: llvm::Operand::Local(uid),
				}
			},
			//Arithmetic and Comparisons between Floats
			(_, llvm::Ty::Float32, llvm::Ty::Float32) | (_, llvm::Ty::Float64, llvm::Ty::Float64) => match bop {
				Equ | Neq | Gt | Gte | Lt | Lte => {
					let uid = gensym("float_cmp");
					ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
						cond: cmp_cond_op(*bop),
						typ: left_result.llvm_typ,
						left: left_result.llvm_op,
						right: right_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Int{bits: 1, signed: false},
						llvm_op: llvm::Operand::Local(uid),
					}
				},
				arith => {
					let uid = gensym("float_arith");
					ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
						op: cmp_binary_op(*arith),
						typ: left_result.llvm_typ,
						left: left_result.llvm_op,
						right: right_result.llvm_op
					}));
					ExpResult{
						llvm_typ: right_result.llvm_typ,
						llvm_op: llvm::Operand::Local(uid),
					}
				}
			},
			(_, llvm::Ty::Float32, llvm::Ty::Float64) => match bop {
				Equ | Neq | Gt | Gte | Lt | Lte => {
					let uid = gensym("float_cmp");
					let extended_uid = gensym("float_ext");
					ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::FloatExt(left_result.llvm_op)));
					ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
						cond: cmp_cond_op(*bop),
						typ: llvm::Ty::Float64,
						left: llvm::Operand::Local(extended_uid),
						right: right_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Float64,
						llvm_op: llvm::Operand::Local(uid),
					}
				},
				_arith => {
					let uid = gensym("float_arith");
					let extended_uid = gensym("float_ext");
					ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::FloatExt(left_result.llvm_op)));
					ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
						op: cmp_binary_op(*bop),
						typ: llvm::Ty::Float64,
						left: llvm::Operand::Local(extended_uid),
						right: right_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Float64,
						llvm_op: llvm::Operand::Local(uid),
					}
				}
			},
			(_, llvm::Ty::Float64, llvm::Ty::Float32) => match bop {
				Equ | Neq | Gt | Gte | Lt | Lte => {
					let uid = gensym("float_cmp");
					let extended_uid = gensym("float_ext");
					ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::FloatExt(right_result.llvm_op)));
					ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
						cond: cmp_cond_op(*bop),
						typ: llvm::Ty::Float64,
						right: llvm::Operand::Local(extended_uid),
						left: left_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Float64,
						llvm_op: llvm::Operand::Local(uid),
					}
				},
				_arith => {
					let uid = gensym("float_arith");
					let extended_uid = gensym("float_ext");
					ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::FloatExt(right_result.llvm_op)));
					ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
						op: cmp_binary_op(*bop),
						typ: llvm::Ty::Float64,
						right: llvm::Operand::Local(extended_uid),
						left: left_result.llvm_op
					}));
					ExpResult{
						llvm_typ: llvm::Ty::Float64,
						llvm_op: llvm::Operand::Local(uid),
					}
				}
			},
			//Pointer arithmetic
			(Add, llvm::Ty::Ptr(pointee_type), llvm::Ty::Int{bits, ..}) | 
			(Sub, llvm::Ty::Ptr(pointee_type), llvm::Ty::Int{bits, ..}) => {
				let ptr_arith_uid = gensym("ptr_arith");
				let offset_op = if *bop == ast2::BinaryOp::Sub {
					let negated_offset_uid = gensym("negated_offset");
					ctxt.stream.push(Component::Instr(negated_offset_uid.clone(), llvm::Instruction::Binop{
						op: llvm::BinaryOp::Mul,
						typ: right_result.llvm_typ.clone(),
						left: right_result.llvm_op,
						right: llvm::Operand::Const(llvm::Constant::SInt{bits: *bits, val: -1})
					}));
					llvm::Operand::Local(negated_offset_uid)
				} else {
					right_result.llvm_op
				};
				ctxt.stream.push(Component::Instr(ptr_arith_uid.clone(), llvm::Instruction::Gep{
					typ: pointee_type.as_ref().clone(),
					base: left_result.llvm_op,
					offsets: vec![
						(right_result.llvm_typ, offset_op)
					]
				}));
				ExpResult{
					llvm_typ: left_result.llvm_typ,
					llvm_op: llvm::Operand::Local(ptr_arith_uid),
				}
			},
			//Pointer Comparison
			(_cond_op, llvm::Ty::Ptr(_), llvm::Ty::Ptr(_)) => {
				let uid = gensym("ptr_cmp");
				ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Cmp{
					cond: cmp_cond_op(*bop),
					typ: left_result.llvm_typ,
					left: left_result.llvm_op,
					right: right_result.llvm_op
				}));
				ExpResult{
					llvm_typ: llvm::Ty::Int{bits: 1, signed: false},
					llvm_op: llvm::Operand::Local(uid),
				}
			},
			_ => panic!("cannot use binop {:?} on llvm types {:?} and {:?}", bop, left_result.llvm_typ, right_result.llvm_typ)
		}
	},
	ast2::Expr::Unop(uop, base) => {
		let base_result = cmp_exp(base, ctxt);
		use ast2::UnaryOp::*;
		match (uop, &base_result.llvm_typ) {
			(Neg, llvm::Ty::Int{bits, signed}) => {
				debug_assert!(*signed, "negating an unsigned int");
				let uid = gensym("neg_int");
				ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
					op: llvm::BinaryOp::Mul,
					typ: llvm::Ty::Int{bits: *bits, signed: *signed},
					left: base_result.llvm_op,
					right: llvm::Operand::Const(llvm::Constant::SInt{bits: *bits, val: -1})
				}));
				ExpResult{
					llvm_typ: base_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
				}
			},
			(Neg, llvm::Ty::Float32) | (Neg, llvm::Ty::Float64) => {
				let uid = gensym("neg_float");
				ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::FloatNeg{
					is_64_bit: base_result.llvm_typ == llvm::Ty::Float64,
					op: base_result.llvm_op
				}));
				ExpResult{
					llvm_typ: base_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
				}
			},
			(Neg, t) => panic!("neg of type {:?}", t),
			(Lognot, llvm::Ty::Int{bits, signed}) => {
				debug_assert!(*bits == 1 && !signed);
				let uid = gensym("lognot");
				ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
					op: llvm::BinaryOp::Sub,
					typ: llvm::Ty::Int{bits: 1, signed: false},
					left: llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: 1}),
					right: base_result.llvm_op
				}));
				ExpResult{
					llvm_typ: base_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
				}
			},
			(Lognot, t) => panic!("neg of type {:?}", t),
			(Bitnot, llvm::Ty::Int{bits, signed}) => {
				let uid = gensym("bitnot");
				ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Binop{
					op: llvm::BinaryOp::Bitxor,
					typ: llvm::Ty::Int{bits: *bits, signed: *signed},
					left: base_result.llvm_op,
					right: llvm::Operand::Const(llvm::Constant::SInt{bits: *bits, val: -1})
				}));
				ExpResult{
					llvm_typ: base_result.llvm_typ,
					llvm_op: llvm::Operand::Local(uid),
				}
			},
			(Bitnot, t) => panic!("lognot of type {:?}", t)
		}
	},
	ast2::Expr::GetRef(nested) => {
		let mut result = cmp_lvalue(nested, ctxt);
		result.llvm_typ = llvm::Ty::Ptr(Box::new(result.llvm_typ));
		result
	},
	ast2::Expr::Sizeof(t) => cmp_sizeof(t, ctxt),
	ast2::Expr::Call(func_name, args) => cmp_call(func_name, args, ctxt, None),
	ast2::Expr::GenericCall{name: func_name, type_param, args} => cmp_call(func_name, args, ctxt, Some(type_param))
}}

fn cmp_sizeof<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>(
		t: &'arena ast2::Ty<'src, 'arena>,
		ctxt: &mut Context<'src, 'arena, 'front, 'func>
		) -> ExpResult<'src, 'arena> {
	/*
	let t: ast::Ty = if t.recursively_find_type_var().is_some() {
		t.replace_type_var_with(ctxt.current_src_type_param().unwrap())
	} else {
		t.clone()
	};
	*/
	if t.is_DST(ctxt.structs, ctxt.mode, ctxt.typecache) {
		//t is dynamically sized, and it is either a GenericStruct, Struct, or Array
		match t {
			ast2::Ty::Array{length, typ} => {
				let mut base_typ_result = cmp_sizeof(typ, ctxt);
				let mul_name = gensym("sizeof_arr_mul");
				ctxt.stream.push(Component::Instr(mul_name.clone(), llvm::Instruction::Binop{
					op: llvm::BinaryOp::Mul,
					typ: llvm::Ty::Int{bits: 64, signed: false},
					left: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: *length}),
					right: base_typ_result.llvm_op
				}));
				base_typ_result.llvm_op = llvm::Operand::Local(mul_name);
				return base_typ_result;
			},
			//if a struct contains an erased struct, it also has a dynamic size
			ast2::Ty::Struct(name) => {
				if let typechecker::StructType::NonGeneric(fields) = ctxt.structs.get(name).unwrap() {
					//I need to pass some type param to cmp_size_of_erased_struct here, using a TypeVar should ensure a crash rather than a miscompile
					let llvm_op = cmp_size_of_erased_struct(fields.iter().map(|(_, t)| *t), ctxt, &ast2::Ty::TypeVar("_should_not_happen"));
					return ExpResult{
						llvm_op,
						llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
					};
				} else {
					panic!("struct context contains generic struct for non-generic struct {}", name);
				}
			},
			ast2::Ty::GenericStruct{type_param, name} => {
				//even separated structs can be DSTs
				if let typechecker::StructType::Generic{fields, ..} = ctxt.structs.get(name).unwrap() {
					let llvm_op = cmp_size_of_erased_struct(fields.iter().map(|(_, t)| *t), ctxt, type_param);
					return ExpResult {
						llvm_op,
						llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
					}
				} else {
					panic!("struct context does not contain a generic struct for '{}'", name);
				}
			},
			ast2::Ty::TypeVar(_) => {
				return ExpResult {
					llvm_op: llvm::Operand::Local(PARAM_SIZE_NAME.to_owned()),
					llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
				};
			},
			_ => panic!("type {} cannot be a DST", t)
		}
	};
	let size_uid = gensym("sizeof");
	let size_int_uid = gensym("sizeof_int");
	let llvm_typ = cmp_ty(t, ctxt.structs, ctxt.current_src_type_param(), ctxt.mode, ctxt.struct_inst_queue, ctxt.typecache);
	let llvm_ptr_typ = llvm::Ty::Ptr(Box::new(llvm_typ.clone()));
	ctxt.stream.push(Component::Instr(size_uid.clone(), llvm::Instruction::Gep{
		typ: llvm_typ.clone(),
		base: llvm::Operand::Const(llvm::Constant::Null(llvm_typ)),
		offsets: vec![
			(llvm::Ty::Int{bits: 32, signed: true}, llvm::Operand::Const(llvm::Constant::SInt{bits: 32, val: 1}))
		]
	}));
	ctxt.stream.push(Component::Instr(size_int_uid.clone(), llvm::Instruction::PtrToInt{
		ptr_ty: llvm_ptr_typ,
		op: llvm::Operand::Local(size_uid)
	}));
	ExpResult{
		llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
		llvm_op: llvm::Operand::Local(size_int_uid),
	}
}

//in an erased function, this is an implicit variable (of type u64) that stores the size of the current type variable
const PARAM_SIZE_NAME: &str = "__param_size";

//in a function that returns a DST, this is an implicit variable that stores the address where the return
//value should be written to. It's actual llvm type is i8*.
const RET_LOC_NAME: &str = "__ret_loc";

//the name of the builtin llvm memcpy function
const LLVM_MEMCPY_FUNC_NAME: &str = "llvm.memcpy.p0i8.p0i8.i64";

//maximum depth for instatiating separated functions
const SEPARATED_FUNC_MAX_DEPTH: u8 = 100;

//This function returns code that computes the size of an erased struct. This function can be used
//to find the offset of a field in a struct by calling it with only the fields that come before the desired field
pub fn cmp_size_of_erased_struct<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>(
		fields: impl IntoIterator<Item = &'arena ast2::Ty<'src, 'arena>>,
		ctxt: &mut Context<'src, 'arena, 'front, 'func>,
		type_param: &'arena ast2::Ty<'src, 'arena>
		) -> llvm::Operand<'src, 'arena> {
	/*
	%acc = 0 + 0
	%acc = %acc + cmp sizeof fields[0]
	%acc = %acc + 7
	%acc = %acc & ~7u64
	%acc = %acc + cmp sizeof fields[1]
	%acc = %acc + 7
	%acc = %acc & ~8u64
	*/
	let mut acc_name = gensym("sizeof_acc");
	ctxt.stream.push(Component::Instr(acc_name.clone(), llvm::Instruction::Binop{
		op: llvm::BinaryOp::Add,
		typ: llvm::Ty::Int{bits: 64, signed: false},
		left: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 0}),
		right: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 0}),
	}));
	for field_ty in fields {
		let added_acc_name = gensym("sizeof_acc");
		let field_ty = field_ty.replace_type_var_with(type_param, ctxt.typecache);
		let sizeof_result = cmp_sizeof(field_ty, ctxt);
		ctxt.stream.push(Component::Instr(added_acc_name.clone(), llvm::Instruction::Binop{
			op: llvm::BinaryOp::Add,
			typ: llvm::Ty::Int{bits: 64, signed: false},
			left: llvm::Operand::Local(acc_name),
			right: sizeof_result.llvm_op
		}));
		let add7_acc_name = gensym("sizeof_acc");
		ctxt.stream.push(Component::Instr(add7_acc_name.clone(), llvm::Instruction::Binop{
			op: llvm::BinaryOp::Add,
			typ: llvm::Ty::Int{bits: 64, signed: false},
			left: llvm::Operand::Local(added_acc_name),
			right: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 7u64})
		}));
		let anded_acc_name = gensym("sizeof_acc");
		ctxt.stream.push(Component::Instr(anded_acc_name.clone(), llvm::Instruction::Binop{
			op: llvm::BinaryOp::Bitand,
			typ: llvm::Ty::Int{bits: 64, signed: false},
			left: llvm::Operand::Local(add7_acc_name),
			right: llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: !7u64})
		}));
		acc_name = anded_acc_name;
	}
	llvm::Operand::Local(acc_name)
}

fn cmp_call<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>(
		func_name: &str,
		args: &'arena [ast2::Loc<ast2::TypedExpr<'src, 'arena>>],
		ctxt: &mut Context<'src, 'arena, 'front, 'func>,
		type_param: Option<&'arena ast2::Ty<'src, 'arena>>
		) -> ExpResult<'src, 'arena> {
	let mut arg_ty_ops: Vec<(llvm::Ty<'src, 'arena>, llvm::Operand<'src, 'arena>)> = Vec::with_capacity(args.len());
	use std::borrow::Cow;
	let (return_type, expected_arg_types, callee_mode) = match ctxt.funcs.get(func_name) {
		Some(typechecker::FuncType::NonGeneric{return_type, args}) => (*return_type, Cow::Borrowed(*args), None),
		Some(typechecker::FuncType::Generic{return_type, args, mode, ..}) => (*return_type, Cow::Borrowed(*args), Some(*mode)),
		None => {
			if PRINTF_FAMILY.contains(&func_name){
				let printf_ret_ty = Some(ast2::Ty::Int{size: ast2::IntSize::Size32, signed: true}.getref(ctxt.typecache));
				let mut printf_expected_args_vec = Vec::with_capacity(args.len());
				let void_ptr = ast2::Ty::Ptr(None).getref(ctxt.typecache);
				for _ in 0..args.len() {
					printf_expected_args_vec.push(void_ptr);
				}
				(printf_ret_ty, Cow::Owned(printf_expected_args_vec), None)
			} else {
				panic!("function {} does not exist", func_name)
			}
		}
	};
	let concretized_type_param: Option<&ast2::Ty<'src, 'arena>> = type_param.map(|t|
		//at this point, the function must be generic because type_param is Some(_)
		if ctxt.mode == Some(ast2::PolymorphMode::Erased) {
			//callee can't be separated, this call is in an erased function
			//if the type param is already concrete, no problem
			//if the type param is not concrete, leave it
			t
		} else {
			t.concretized(ctxt.current_src_type_param(), ctxt.typecache)
		}
	);
	/*
	when calling an erased function, any 'T in the type signature that is behind a sequence of pointers needs to have the 'T
	converted to i8. When calling the erased function, any arguments that contain a 'T but are not DSTs must be a sequence of pointers,
	and should be bitcasted to a a type with the same number of pointers, but with the root type replaced with i8. If the return
	value contains a 'T but is not a DST, then bitcast from Ptrchain...(i8) to Ptrchain...(expected type)
	*/
	#[allow(non_snake_case)]
	fn depth_of_DST_in_ptr_chain<'src: 'arena, 'arena>(t: &ast2::Ty<'src, 'arena>, structs: &typechecker::StructContext<'src, 'arena>, mode: Option<ast2::PolymorphMode>, typecache: &'arena ast2::TypeCache<'src, 'arena>) -> Option<usize> {
		match t {
			ast2::Ty::Ptr(Some(t)) => depth_of_DST_in_ptr_chain(t, structs, mode, typecache).map(|i| i+1),
			other if other.is_DST(structs, mode, typecache) => Some(0),
			_ => None
		}
	}
	for (arg, expected_ty) in args.iter().zip(expected_arg_types.as_ref()) {
		//if arg is dynamically sized, then arg_result will be a ptr to that value, which is what should be passed to the function
		//however, the type used for this operand should be i8*, not i8 (really Dynamic(_), but gets printed as i8)
		let arg_result = cmp_exp(arg, ctxt);
		if matches!(arg_result.llvm_typ, llvm::Ty::Dynamic(_)) {
			arg_ty_ops.push( (llvm::Ty::Ptr(Box::new(arg_result.llvm_typ)), arg_result.llvm_op) );
		} else if expected_ty.is_DST(ctxt.structs, callee_mode, ctxt.typecache) {
			//if arg is statically sized in the caller, but dynamically sized in the callee, alloca enough space for it
			//store it, then pass the address to the function
			let alloca_uid = gensym("callee_DST");
			ctxt.stream.push(Component::Instr(alloca_uid.clone(), llvm::Instruction::Alloca(
				arg_result.llvm_typ.clone(), llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 1}), None
			)));
			ctxt.stream.push(Component::Instr(String::new(), llvm::Instruction::Store{
				typ: arg_result.llvm_typ.clone(),
				data: arg_result.llvm_op,
				dest: llvm::Operand::Local(alloca_uid.clone())
			}));
			let i8_ptr: llvm::Ty = llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}));
			let bitcasted_uid = gensym("callee_bitcast");
			ctxt.stream.push(Component::Instr(bitcasted_uid.clone(), llvm::Instruction::Bitcast{
				original_typ: llvm::Ty::Ptr(Box::new(arg_result.llvm_typ)),
				op: llvm::Operand::Local(alloca_uid),
				new_typ: i8_ptr.clone()
			}));
			arg_ty_ops.push( (i8_ptr, llvm::Operand::Local(bitcasted_uid)) );
		} else {
			//the arg is statically sized in both the caller and the callee
			//however, the arg could be a ptr to something that is a DST in the callee, so the caller and callee
			//could disagree on its type (i.e. caller sees an i32**, callee sees a 'T**, thus a i8**). In this case,
			//bitcast the arg to a i8*...*
			if let Some(ptr_chain_len) = depth_of_DST_in_ptr_chain(expected_ty, ctxt.structs, callee_mode, ctxt.typecache) {
				let mut ptr_chain = llvm::Ty::Int{bits: 8, signed: false};
				for _ in 0..ptr_chain_len {
					ptr_chain = llvm::Ty::Ptr(Box::new(ptr_chain));
				}
				//%bitcasted_chain = bitcast arg_result.llvm_typ arg_result.llvm_op to ptr_chain
				let bitcasted_chain_uid = gensym("ptr_chain");
				ctxt.stream.push(Component::Instr(bitcasted_chain_uid.clone(), llvm::Instruction::Bitcast{
					original_typ: arg_result.llvm_typ,
					op: arg_result.llvm_op,
					new_typ: ptr_chain.clone()
				}));
				arg_ty_ops.push((ptr_chain, llvm::Operand::Local(bitcasted_chain_uid)))
			} else {
				arg_ty_ops.push((arg_result.llvm_typ, arg_result.llvm_op));
			}
		}
	}
	let uid = gensym("call");
	let mut dst_result_uid: Option<String> = None;
	let (result_is_dst, llvm_ret_ty, result_needs_ptr_chain_bitcast) = match return_type {
		None => (false, llvm::Ty::Void, false),
		Some(t) if t.is_DST(ctxt.structs, callee_mode, ctxt.typecache) => {
			//compute the size of this type, alloca this much space, pass the pointer as an extra arg
			//if the func context claims that `func_name` returns a 'T, but the type param for this call is i16, then replace
			let replaced_return_type: &ast2::Ty<'_, '_> = t.replace_type_var_with(concretized_type_param.unwrap_or_else(|| ast2::Ty::TypeVar("_should_not_happen").getref(ctxt.typecache)), ctxt.typecache);
			let ExpResult{llvm_op: sizeof_op, ..} = cmp_sizeof(replaced_return_type, ctxt);
			let result_addr_uid = gensym("DST_retval_result");
			dst_result_uid = Some(result_addr_uid.clone());
			ctxt.stream.push(Component::Instr(result_addr_uid.clone(), llvm::Instruction::Alloca(
				llvm::Ty::Int{bits: 8, signed: false}, sizeof_op, Some(8)
			)));
			arg_ty_ops.push( (llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})), llvm::Operand::Local(result_addr_uid)) );
			(true, llvm::Ty::Void, false)
		},
		Some(t) => {
			//if the function being called is separated and has a return type of struct A@<'T>, and the function call
			//looks like f@<i32>(), then use i32 as the type var replacement when cmping the return type

			/*
			whenever dealing with a type that is part of a separated function (either cmp_func called on a separated function,
			cmp_call called on a call to a separated function, or just wherever ctxt.current_separated_type_param == Some(_)),
			if the type is a separated struct, I need to recursively replace any TypeVars in its type parameter with the function's
			type parameter
			EX: inside of the separated function f, instantiating it with type param u8, and I encounter a declaration of a struct vec@<'T*>,
			before I call cmp_ty on that type, I need to replace 'T with u8
			idea: pass Some(&u8) to cmp_ty, it will call replace_type_var_with
			it turns out this was a bad idea (cmp_ty becomes a mess), so I will do this whenever interacting with a generic thing,
			which I think will just be when calling a generic function, cmping a generic function, Proj on a generic struct,
			Sizeof, Cast
			*/
			(
				false,
				//NOTE: was using ctxt.mode here, now trying out callee_mode. This seems to work
				cmp_ty(t, ctxt.structs, concretized_type_param, callee_mode, ctxt.struct_inst_queue, ctxt.typecache),
				depth_of_DST_in_ptr_chain(t, ctxt.structs, callee_mode, ctxt.typecache).is_some()
			)
		}
	};
	if callee_mode == Some(ast2::PolymorphMode::Erased) {
		let call_type_param = concretized_type_param.unwrap();
		//compute the size of the type param
		let ExpResult{llvm_op: sizeof_op, ..} = cmp_sizeof(call_type_param, ctxt);
		arg_ty_ops.push( (llvm::Ty::Int{bits: 64, signed: false}, sizeof_op) );
	}
	if callee_mode == Some(ast2::PolymorphMode::Separated) {
		//add this function instatiation to the func queue
		ctxt.func_inst_queue.lock().unwrap().push(func_name.to_string(), concretized_type_param.unwrap(), ctxt.current_separated_func_depth + 1);
	}
	let possibly_mangled_name: String = match callee_mode {
		None | Some(ast2::PolymorphMode::Erased) => func_name.to_owned(),
		Some(ast2::PolymorphMode::Separated) => {
			let mut possibly_replaced_type_param = concretized_type_param.unwrap();
			match ctxt.current_src_type_param() {
				None => debug_assert!(type_param.unwrap().recursively_find_type_var().is_none(), "ctxt has not separated type param, but type param in a generic struct has a type var in it, {:?}", type_param),
				Some(replacement) => {
					possibly_replaced_type_param = possibly_replaced_type_param.replace_type_var_with(replacement, ctxt.typecache);
				}
			};
			mangle(func_name, possibly_replaced_type_param)
		}
	};
	ctxt.stream.push(Component::Instr(uid.clone(), llvm::Instruction::Call{
		func_name: possibly_mangled_name,
		ret_typ: llvm_ret_ty.clone(),
		args: arg_ty_ops
	}));
	if result_is_dst {
		//the callee returns a Dynamic(TypeVar("T")) by memcpy, but I know that 'T is i16,
		//so I need to load from the dst return location as an i16
		//if 'T was still dynamic in the caller context, then don't load from the dst return location,
		//just change the llvm_typ from Dynamic(TypeVar("T")) to Dynamic(type_param)
		if callee_mode == Some(ast2::PolymorphMode::Erased) {
			let call_type_param = concretized_type_param.unwrap();
			let replaced_result_ty = return_type.as_ref().unwrap().replace_type_var_with(call_type_param, ctxt.typecache);
			if !replaced_result_ty.is_DST(ctxt.structs, Some(ast2::PolymorphMode::Erased), ctxt.typecache) {
				//replacing the type var in the return type makes it no longer a DST
				let static_llvm_ty = cmp_ty(replaced_result_ty, ctxt.structs, ctxt.current_src_type_param(), Some(ast2::PolymorphMode::Erased), ctxt.struct_inst_queue, ctxt.typecache);
				let cast_op = gensym("bitcast");
				ctxt.stream.push(Component::Instr(cast_op.clone(), llvm::Instruction::Bitcast{
					original_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})),
					op: llvm::Operand::Local(dst_result_uid.unwrap()),
					new_typ: llvm::Ty::Ptr(Box::new(static_llvm_ty.clone()))
				}));
				let loaded_op = gensym("static_type_load");
				ctxt.stream.push(Component::Instr(loaded_op.clone(), llvm::Instruction::Load{
					typ: static_llvm_ty.clone(),
					src: llvm::Operand::Local(cast_op)
				}));
				return ExpResult{
					llvm_typ: static_llvm_ty,
					llvm_op: llvm::Operand::Local(loaded_op),
				};
			}
			//if the type is still dynamic, just change the llvm type, but it will still be a Dynamic(_)
		}
		ExpResult{
			llvm_typ: llvm::Ty::Dynamic(return_type.unwrap().concretized(concretized_type_param, ctxt.typecache)),
			llvm_op: llvm::Operand::Local(dst_result_uid.unwrap()),
		}
	} else if result_needs_ptr_chain_bitcast {
		//llvm_ret_ty will be i8*...* callee's src return type could be {any DST}*..*
		let caller_src_ret_ty = return_type.unwrap().concretized(type_param, ctxt.typecache);
		if caller_src_ret_ty.is_DST(ctxt.structs, ctxt.mode, ctxt.typecache) {
			//if the base of the ptr chain in the caller is still a dst, don't do anything
			ExpResult{
				llvm_typ: llvm_ret_ty,
				llvm_op: llvm::Operand::Local(uid),
			}
		} else {
			//the caller is not expecting a DST, so bitcast
			let caller_llvm_ret_ty = cmp_ty(caller_src_ret_ty, ctxt.structs, ctxt.current_src_type_param(), ctxt.mode, ctxt.struct_inst_queue, ctxt.typecache);
			let bitcasted_chain_uid = gensym("ptr_chain_ret");
			ctxt.stream.push(Component::Instr(bitcasted_chain_uid.clone(), llvm::Instruction::Bitcast{
				original_typ: llvm_ret_ty,
				op: llvm::Operand::Local(uid),
				new_typ: caller_llvm_ret_ty.clone()
			}));
			ExpResult{
				llvm_typ: caller_llvm_ret_ty,
				llvm_op: llvm::Operand::Local(bitcasted_chain_uid),
			}
		}
	} else {
		ExpResult{
			llvm_typ: llvm_ret_ty,
			llvm_op: llvm::Operand::Local(uid),
		}
	}
}

//the op this function returns is a pointer to where the data is stored
//the llvm::Ty this function returns is the type of the thing being pointed to, it may not be a Ptr
fn cmp_lvalue<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>(
		e: &'arena ast2::TypedExpr<'src, 'arena>,
		ctxt: &mut Context<'src, 'arena, 'front, 'func>
		) -> ExpResult<'src, 'arena> { match &e.expr {
	ast2::Expr::Id(s) => {
		if *s == "errno" {
			let op = gensym("errno_loc");
			ctxt.stream.push(Component::Instr(op.clone(), llvm::Instruction::Call{
				func_name: ctxt.errno_func_name.to_owned(),
				ret_typ: llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 32, signed: true})),
				args: vec![]
			}));
			return ExpResult{
				llvm_typ: llvm::Ty::Int{bits: 32, signed: true},
				llvm_op: llvm::Operand::Local(op),
			}
		}
		let (ll_ty, ll_op) = ctxt.get_var(s);
		ExpResult{
			llvm_typ: ll_ty.clone(),
			llvm_op: ll_op.clone(),
		}
	},
	ast2::Expr::Index(base, index) => {
		let mut base_lvalue_result;
		if !matches!(&base.expr, ast2::Expr::Id(_) | ast2::Expr::Index(_,_) | ast2::Expr::Proj(_,_) | ast2::Expr::Deref(_)) {
			//if base is a function call, then it must return a pointer
			base_lvalue_result = cmp_exp(base, ctxt);
		} else {
			//if base is a potential lvalue, then cmp it as an lvalue, see what it's type is,
			//and potentially load from it if its type is a pointer
			base_lvalue_result = cmp_lvalue(base, ctxt);
			match &base_lvalue_result.llvm_typ {
				llvm::Ty::Dynamic(ast2::Ty::Array{typ: nested_dynamic_type, ..}) => {
					//need to change base_lvalue_result to make its llvm_typ a Ptr(Dynamic(nested_dynamic_type))
					//don't have to emit any instructions, because it would just bitcast from i8* to i8*
					base_lvalue_result.llvm_typ = llvm::Ty::Ptr(Box::new(llvm::Ty::Dynamic(nested_dynamic_type)));
				},
				//if base is an array, convert it to a pointer to the first element
				llvm::Ty::Array{typ, ..} => {
					let decay_id = gensym("arr_decay");
					ctxt.stream.push(Component::Instr(decay_id.clone(), llvm::Instruction::Bitcast{
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
					ctxt.stream.push(Component::Instr(loaded_id.clone(), llvm::Instruction::Load{
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
		let mut index_result = cmp_exp(index, ctxt);
		let result_op = gensym("index_offset");
		let result_typ = base_lvalue_result.llvm_typ.remove_ptr();
		if let llvm::Ty::Dynamic(dst) = &result_typ {
			let ExpResult{llvm_op: sizeof_op, ..} = cmp_sizeof(dst, ctxt);
			let (index_result_bits, signed) = match index_result.llvm_typ {
				llvm::Ty::Int{bits, signed} => (bits, signed),
				_ => panic!("array index's llvm_typ is not an integer")
			};
			if index_result_bits < 64 {
				let extended_uid = gensym("extended");
				ctxt.stream.push(Component::Instr(extended_uid.clone(), llvm::Instruction::Ext{
					old_bits: index_result_bits,
					op: index_result.llvm_op,
					new_bits: 64,
					signed
				}));
				index_result.llvm_op = llvm::Operand::Local(extended_uid);
				index_result.llvm_typ = llvm::Ty::Int{bits: 64, signed};
			}
			let mul_uid = gensym("dyn_index_mul");
			ctxt.stream.push(Component::Instr(mul_uid.clone(), llvm::Instruction::Binop{
				op: llvm::BinaryOp::Mul,
				typ: index_result.llvm_typ,
				left: index_result.llvm_op,
				right: sizeof_op
			}));
			let add_uid = gensym("dyn_index_add");
			ctxt.stream.push(Component::Instr(add_uid.clone(), llvm::Instruction::Gep{
				typ: llvm::Ty::Int{bits: 8, signed: false},
				base: base_lvalue_result.llvm_op,
				offsets: vec![(llvm::Ty::Int{bits: 64, signed: false}, llvm::Operand::Local(mul_uid))]
			}));
			ExpResult{
				llvm_typ: result_typ,
				llvm_op: llvm::Operand::Local(add_uid),
			}
		} else {
			ctxt.stream.push(Component::Instr(result_op.clone(), llvm::Instruction::Gep{
				typ: result_typ.clone(),
				base: base_lvalue_result.llvm_op,
				offsets: vec![(index_result.llvm_typ, index_result.llvm_op)]
			}));
			ExpResult{
				llvm_typ: result_typ,
				llvm_op: llvm::Operand::Local(result_op),
			}
		}

	},
	ast2::Expr::Proj(base, field_name) => {
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
		if !matches!(&base.expr, ast2::Expr::Id(_) | ast2::Expr::Index(_,_) | ast2::Expr::Proj(_,_) | ast2::Expr::Deref(_)) {
			base_lvalue_result = cmp_exp(base, ctxt);
		} else {
			base_lvalue_result = cmp_lvalue(base, ctxt);
			match &base_lvalue_result.llvm_typ {
				llvm::Ty::Dynamic(_) => (), //if loading from the base operand would yield a DST, don't do anything
				llvm::Ty::NamedStruct(_, _, _) => (), //if base points to a struct directly, don't do anything
				llvm::Ty::Ptr(boxed) => match boxed as &llvm::Ty {
					llvm::Ty::NamedStruct(_, _, _) | llvm::Ty::Dynamic(_) => {
						let loaded_id = gensym("struct_deref");
						ctxt.stream.push(Component::Instr(loaded_id.clone(), llvm::Instruction::Load{
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
		let mut base_type_param: Option<&ast2::Ty<'_, '_>> = None;
		let struct_name: &str = match &base_lvalue_result.llvm_typ {
			llvm::Ty::Dynamic(t) => {
				is_dynamic = true;
				match t {
					ast2::Ty::Struct(s) => s,
					ast2::Ty::GenericStruct{name, type_param} => {
						base_type_param = Some(type_param);
						name
					},
					t => panic!("Cannot do a dynamic proj off of type {:?}", t)
				}
			},
			llvm::Ty::NamedStruct(_llvm_name, src_name, type_param) => {
				base_type_param = *type_param;
				src_name
			},
			llvm::Ty::Ptr(boxed) => match boxed as &llvm::Ty {
				llvm::Ty::Dynamic(t) => {
					is_dynamic = true;
					match t {
						ast2::Ty::Struct(s) => s,
						ast2::Ty::GenericStruct{name, type_param} => {
							base_type_param = Some(type_param);
							name
						},
						t => panic!("Cannot do a dynamic proj off of type {:?}", t)
					}
				}
				llvm::Ty::NamedStruct(_llvm_name, src_name, type_param) => {
					base_type_param = *type_param;
					src_name
				},
				t => panic!("Proj base has llvm type Ptr({:?})", t)
			}
			t => panic!("Proj base has llvm type {:?}", t)
		};
		//base_lvalue_result is now the address of the struct, just need to do one more Gep
		let fields: &[(_, &ast2::Ty<'_, '_>)] = match ctxt.structs.get(struct_name) {
			None => panic!("struct {} not in struct_context", &struct_name),
			Some(typechecker::StructType::NonGeneric(fields)) => fields,
			Some(typechecker::StructType::Generic{fields, ..}) => fields
		};
		let mut field_index: Option<usize> = None;
		for (i, (name, _src_ty)) in fields.iter().enumerate() {
			if name == &field_name.elt {
				field_index = Some(i);
				break;
			}
		}
		let field_index: usize = field_index.unwrap_or_else(|| panic!("field name {} not found in struct {}", field_name, struct_name));
		if is_dynamic {
			let preceding_fields_iter = fields.iter().take(field_index).map(|(_, t)| *t);
			let base_type_param = base_type_param.unwrap_or_else(|| ast2::Ty::TypeVar("_should_not_happen").getref(ctxt.typecache));
			let offset_op = cmp_size_of_erased_struct(preceding_fields_iter, ctxt, base_type_param);
			let ptr_offset_op = gensym("DST_offset");
			ctxt.stream.push(Component::Instr(ptr_offset_op.clone(), llvm::Instruction::Gep{
				typ: llvm::Ty::Int{bits: 8, signed: false},
				base: base_lvalue_result.llvm_op,
				offsets: vec![(llvm::Ty::Int{bits: 64, signed: false}, offset_op)]
			}));
			let field_type: &ast2::Ty<'_, '_> = fields[field_index].1;
			base_lvalue_result.llvm_typ = cmp_ty(field_type, ctxt.structs,
				//if the base type is a regular struct that is dynamic, then don't need to pass a
				//replacement type here, otherwise the type parameter must be cmped
				Some(base_type_param),
				ctxt.mode,
				ctxt.struct_inst_queue,
				ctxt.typecache
			);
			let bitcasted_uid = gensym("DST_proj_bitcast");
			ctxt.stream.push(Component::Instr(bitcasted_uid.clone(), llvm::Instruction::Bitcast{
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
		let result_ty = cmp_ty(fields[field_index].1, ctxt.structs, base_type_param, ctxt.mode, ctxt.struct_inst_queue, ctxt.typecache);
		let field_index: u64 = u64::try_from(field_index).expect("could not convert from usize to u64");
		let field_addr_uid = gensym("field");
		let possibly_mangled_name = match base_type_param {
			None => struct_name.to_owned(),
			Some(t) => {
				let mut possibly_replaced_type_param = t;
				match ctxt.current_src_type_param() {
					None => debug_assert!(t.recursively_find_type_var().is_none(), "ctxt has not separated type param, but type param in a generic struct has a type var in it, {:?}", t),
					Some(replacement) => {
						possibly_replaced_type_param = possibly_replaced_type_param.replace_type_var_with(replacement, ctxt.typecache)
					}
				};
				mangle(struct_name, possibly_replaced_type_param)
			}
		};
		ctxt.stream.push(Component::Instr(field_addr_uid.clone(), llvm::Instruction::Gep{
			//String::new() and None here will not be inspected for type info, so they can be set to dummy values
			//the llvm code printer will ignore them
			typ: llvm::Ty::NamedStruct(possibly_mangled_name, String::new(), None),
			base: base_lvalue_result.llvm_op,
			offsets: vec![
				(llvm::Ty::Int{bits: 1, signed: false}, llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: 0})),
				(llvm::Ty::Int{bits: 32, signed: false}, llvm::Operand::Const(llvm::Constant::UInt{bits: 32, val: field_index}))
			]
		}));
		ExpResult{
			llvm_typ: result_ty,
			llvm_op: llvm::Operand::Local(field_addr_uid),
		}
	},
	ast2::Expr::Deref(base) => {
		let mut result = cmp_exp(base, ctxt);
		result.llvm_typ = result.llvm_typ.remove_ptr();
		result
	},
	other => panic!("{:?} is not a valid lvalue", other)
}}

fn cmp_lvalue_to_rvalue<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>(
		e: &'arena ast2::TypedExpr<'src, 'arena>,
		gensym_seed: &str, 
		ctxt: &mut Context<'src, 'arena, 'front, 'func>
		) -> ExpResult<'src, 'arena> {
	let mut lvalue_result = cmp_lvalue(e, ctxt);
	if matches!(lvalue_result.llvm_typ, llvm::Ty::Dynamic(_)) {
		//when dealing with rvalues, if it's llvm type is Dynamic(_), then the operand is a pointer
		//to the data, not the data itself
		return lvalue_result;
	}
	let loaded_id = gensym(gensym_seed);
	//lvalue_result.llvm_typ = lvalue_result.llvm_typ.remove_ptr();
	ctxt.stream.push(
		Component::Instr(loaded_id.clone(), llvm::Instruction::Load{
			typ: lvalue_result.llvm_typ.clone(),
			src: lvalue_result.llvm_op
		})
	);
	//don't need to change the typ, it is already the type of the var
	lvalue_result.llvm_op = llvm::Operand::Local(loaded_id);
	lvalue_result
}

fn cmp_binary_op(bop: ast2::BinaryOp) -> llvm::BinaryOp {
	use ast2::BinaryOp as SrcOp;
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

fn cmp_cond_op(bop: ast2::BinaryOp) -> llvm::Cond {
	use ast2::BinaryOp as SrcOp;
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

fn cmp_stmt<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>(
		stmt: &'arena ast2::Stmt<'src, 'arena>, 
		ctxt: &mut Context<'src, 'arena, 'front, 'func>,
		expected_ret_ty: &llvm::Ty<'src, 'arena>
		) { match stmt {
	ast2::Stmt::Assign(lhs, rhs) => {
		let dest_result = cmp_lvalue(lhs, ctxt);
		let data_result = cmp_exp(rhs, ctxt);
		#[cfg(debug_assertions)]
		if dest_result.llvm_typ != data_result.llvm_typ {
			eprintln!("BUG: Assignment type discrepancy on when cmping {:?} = {:?};", lhs, rhs);
			eprintln!("dest_result.llvm_typ = {:?}", dest_result.llvm_typ);
			eprintln!("data_result.llvm_typ = {:?}", data_result.llvm_typ);
		}
		if let llvm::Ty::Dynamic(dst) = data_result.llvm_typ {
			let ExpResult{llvm_op: sizeof_op, ..} = cmp_sizeof(dst, ctxt);
			//memcpy(dest_result.llvm_op, data_result.llvm_op, sizeof_result.llvm_op);
			let i8_ptr: llvm::Ty = llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}));
			ctxt.stream.push(Component::Instr(String::new(), llvm::Instruction::Call{
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
			ctxt.stream.push(Component::Instr(String::new(), llvm::Instruction::Store{
				typ: data_result.llvm_typ,
				data: data_result.llvm_op,
				dest: dest_result.llvm_op
			}));
		}
	},
	ast2::Stmt::Decl(typ, var_name) => {
		let uid = gensym(format!("{}_loc", var_name).as_str());
		if typ.is_DST(ctxt.structs, ctxt.mode, ctxt.typecache) {
			//this declaration requires dynamic alloca
			let llvm_typ = llvm::Ty::Dynamic(typ);
			ctxt.locals.insert(var_name.to_string(), (llvm_typ, llvm::Operand::Local(uid.clone())));
			let sizeof_result = cmp_sizeof(typ, ctxt);
			ctxt.stream.push(Component::Instr(uid, llvm::Instruction::Alloca(
				llvm::Ty::Int{bits: 8, signed: false}, sizeof_result.llvm_op, Some(8)
			)));
		} else {
			//even if the type is not dynamically sized, it could be a pointer to a DST,
			//and cmp_ty will yield a Ptr(llvm::Ty::Dynamic). It is OK to have Dynamic(_) llvm types in the stream, because
			//when the llvm code is emitted, Dynamic(_) will be printed as i8, so there is no need to recurse over `llvm_typ` and
			//replace any Dynamic(_) with i8
			let llvm_typ = cmp_ty(typ, ctxt.structs, ctxt.current_src_type_param(), ctxt.mode, ctxt.struct_inst_queue, ctxt.typecache);
			ctxt.locals.insert(var_name.to_string(), (llvm_typ.clone(), llvm::Operand::Local(uid.clone())));
			//replace_dynamic_with_i8(&mut llvm_typ);
			ctxt.stream.push(Component::Instr(uid, llvm::Instruction::Alloca(llvm_typ, llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 1}), None)))
		}
	},
	ast2::Stmt::Return(Some(expr)) => {
		let expr_result = cmp_exp(expr, ctxt);
		if let llvm::Ty::Dynamic(dst) = expr_result.llvm_typ {
			//there will be an llvm local that indicates where to write the result to
			//There will also be an llvm local that indicates the size to memcpy
			//Recomputing the size allows LLVM to optimize it down to a constant, but using
			//the local means the frontend has to do less work.
			let ExpResult{llvm_op: sizeof_op, ..} = cmp_sizeof(dst, ctxt);
			let i8_ptr = llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}));
			ctxt.stream.push(Component::Instr(String::new(), llvm::Instruction::Call{
				func_name: LLVM_MEMCPY_FUNC_NAME.to_owned(),
				ret_typ: llvm::Ty::Void,
				args: vec![
					(i8_ptr.clone(), llvm::Operand::Local(RET_LOC_NAME.to_owned())),
					(i8_ptr, expr_result.llvm_op),
					(llvm::Ty::Int{bits: 64, signed: false}, sizeof_op),
					(llvm::Ty::Int{bits: 1, signed: false}, llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: 0}))
				]
			}));
			ctxt.stream.push(Component::Term(llvm::Terminator::Ret(None)));
			ctxt.stream.push(Component::Label(gensym("unreachable_after_return")));
		} else { //not returning a DST
			ctxt.stream.push(Component::Term(llvm::Terminator::Ret(
				Some((expr_result.llvm_typ, expr_result.llvm_op))
			)));
			ctxt.stream.push(Component::Label(gensym("unreachable_after_return")));
		}
	},
	ast2::Stmt::Return(None) => {
		ctxt.stream.push(Component::Term(llvm::Terminator::Ret(None)));
		ctxt.stream.push(Component::Label(gensym("unreachable_after_return")));
	},
	ast2::Stmt::SCall(func_name, args) => {
		cmp_call(func_name, args, ctxt, None);
	},
	ast2::Stmt::GenericSCall{name: func_name, type_param, args} => {
		cmp_call(func_name, args, ctxt, Some(type_param));
	},
	ast2::Stmt::If(cond, then_block, else_block) => {
		let cond_result = cmp_exp(cond, ctxt);
		let then_lbl = gensym("then");
		let else_lbl = gensym("else");
		let merge_lbl = gensym("merge");
		//stream.reserve(then_stream.len() + else_stream.len() + 6);
		ctxt.stream.push(Component::Term(llvm::Terminator::CondBr{
			condition: cond_result.llvm_op,
			true_dest: then_lbl.clone(),
			false_dest: else_lbl.clone(),
		}));
		ctxt.stream.push(Component::Label(then_lbl));
		cmp_block(then_block, ctxt, expected_ret_ty);
		ctxt.stream.push(Component::Term(llvm::Terminator::Br(merge_lbl.clone())));
		ctxt.stream.push(Component::Label(else_lbl));
		cmp_block(else_block, ctxt, expected_ret_ty);
		ctxt.stream.push(Component::Term(llvm::Terminator::Br(merge_lbl.clone())));
		ctxt.stream.push(Component::Label(merge_lbl));
	},
	ast2::Stmt::While(cond, body) => {
		let check_lbl = gensym("check_cond");
		let body_lbl = gensym("body");
		let after_lbl = gensym("after");
		//stream.reserve(cond_result.stream.len() + body_stream.len() + 6);
		ctxt.stream.push(Component::Term(llvm::Terminator::Br(check_lbl.clone())));
		ctxt.stream.push(Component::Label(check_lbl.clone()));
		let cond_result = cmp_exp(cond, ctxt);
		ctxt.stream.push(Component::Term(llvm::Terminator::CondBr{
			condition: cond_result.llvm_op,
			true_dest: body_lbl.clone(),
			false_dest: after_lbl.clone()
		}));
		ctxt.stream.push(Component::Label(body_lbl));
		cmp_block(body, ctxt, expected_ret_ty);
		ctxt.stream.push(Component::Term(llvm::Terminator::Br(check_lbl)));
		ctxt.stream.push(Component::Label(after_lbl));
	}
}}

fn cmp_block<'src: 'arena, 'arena: 'front, 'front: 'func, 'func>(block: &'arena ast2::Block<'src, 'arena>, ctxt: &mut Context<'src, 'arena, 'front, 'func>, expected_ret_ty: &llvm::Ty<'src, 'arena>) {
	for stmt in block.0.iter() {
		cmp_stmt(stmt, ctxt, expected_ret_ty);
	}
}


//functions and type defs can have the same name, so only one mangling function is needed
fn mangle<'src: 'arena, 'arena>(name: &str, ty: &ast2::Ty<'src, 'arena>) -> String {
	fn mangle_type<'src: 'arena, 'arena>(t: &ast2::Ty<'src, 'arena>, output: &mut String) {
		use ast2::Ty::*;
		use std::fmt::Write;
		//if it ends in ., it's a pointer
		//if it ends in .123, it's an array
		//if it ends in .struct, it's a struct
		match t {
			Bool | Int{..} | Float(_) => write!(output, "{}", t).unwrap(),
			Ptr(None) => output.push_str("void."),
			Ptr(Some(nested)) => {
				mangle_type(nested, output);
				output.push('.');
			},
			Array{length, typ: nested} => {
				mangle_type(nested, output);
				output.push('.');
				write!(output, "{}", length).unwrap()
			},
			Struct(s) => {
				output.push_str(s);
				output.push_str(".struct");
			},
			GenericStruct{type_param, name} => {
				output.push_str(name);
				output.push('$');
				mangle_type(type_param, output);
			},
			TypeVar(s) => panic!("Cannot mangle a TypeVar {}", s),
		}
	}
	let mut result_string = name.to_owned();
	result_string.push('$');
	mangle_type(ty, &mut result_string);
	result_string
}

#[derive(Clone, Copy)]
enum FuncInst<'src: 'arena, 'arena>{
	NonGeneric(&'arena ast2::Func<'src, 'arena>),
	Erased(&'arena ast2::GenericFunc<'src, 'arena>),
	Separated(&'arena ast2::GenericFunc<'src, 'arena>, &'arena ast2::Ty<'src, 'arena>, u8)
}
fn cmp_func<'src: 'arena, 'arena: 'front, 'front>(f: FuncInst<'src, 'arena>, 
			prog_context: &'arena typechecker::ProgramContext<'src, 'arena>,
			global_locs: &'front HashMap<String, (llvm::Ty<'src, 'arena>, llvm::Operand<'src, 'arena>)>,
			struct_inst_queue: &'front Mutex<SeparatedStructInstQueue<'src, 'arena>>,
			func_inst_queue: &'front Mutex<SeparatedFuncInstQueue<'src, 'arena>>,
			errno_func_name: &'src str,
			typecache: &'arena ast2::TypeCache<'src, 'arena>)
			-> (llvm::Func<'src, 'arena>, Vec<(String, llvm::GlobalDecl<'src, 'arena>)>) {
	//compiling a non-generic function and an erased function are nearly the same thing, but PARAM_SIZE_NAME needs to be added to the params
	let mut context = Context{
		locals: HashMap::new(),
		globals: global_locs,
		funcs: &prog_context.funcs,
		structs: &prog_context.structs,
		mode: None,
		struct_inst_queue,
		func_inst_queue,
		current_separated_type_param: None,
		current_separated_func_depth: 0,
		errno_func_name,
		stream: Vec::new(),
		typecache,
		_must_use_func_placeholder: &std::marker::PhantomData
	};
	let (args, ret_ty, func_name, body) = match f {
		FuncInst::NonGeneric(f) => (&f.args, &f.ret_type, &f.name as &str, &f.body),
		FuncInst::Erased(f) => {context.mode = Some(ast2::PolymorphMode::Erased); (&f.args, &f.ret_type, &f.name as &str, &f.body)},
		FuncInst::Separated(f,type_param, depth) => {
			context.mode = Some(ast2::PolymorphMode::Separated);
			context.current_separated_type_param = Some((type_param, cmp_ty(type_param, &prog_context.structs, None, context.mode, context.struct_inst_queue, typecache)));
			context.current_separated_func_depth = depth;
			(&f.args, &f.ret_type, &f.name as &str, &f.body)
		}
	};
	context.stream = Vec::with_capacity(args.len() * 2);
	let mut params = Vec::with_capacity(args.len());
	let (ret_is_dst, ll_ret_ty) = match ret_ty.elt {
		None => (false, llvm::Ty::Void),
		Some(t) if t.is_DST(&prog_context.structs, context.mode, typecache) => (true, llvm::Ty::Void),
		Some(t) => (false, cmp_ty(t, &prog_context.structs, context.current_src_type_param(), context.mode, context.struct_inst_queue, typecache))
	};
	for (arg_ty, arg_name) in args.iter() {
		if arg_ty.is_DST(&prog_context.structs, context.mode, typecache) {
			let ExpResult{llvm_op: sizeof_op, ..} = cmp_sizeof(arg_ty, &mut context);
			//alloca enough space for this type
			let dst_copy_uid = gensym("dst_param_copy");
			context.stream.push(Component::Instr(dst_copy_uid.clone(), llvm::Instruction::Alloca(
				llvm::Ty::Int{bits: 8, signed: false}, sizeof_op.clone(), Some(8)
			)));
			let ll_arg_id = gensym("arg");
			//memcpy from %ll_arg_id to %dst_copy_uid
			let i8_ptr: llvm::Ty = llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}));
			context.stream.push(Component::Instr(String::new(), llvm::Instruction::Call{
				func_name: LLVM_MEMCPY_FUNC_NAME.to_owned(),
				ret_typ: llvm::Ty::Void,
				args: vec![
					(i8_ptr.clone(), llvm::Operand::Local(dst_copy_uid.clone())),
					(i8_ptr.clone(), llvm::Operand::Local(ll_arg_id.clone())),
					(llvm::Ty::Int{bits: 64, signed: false}, sizeof_op),
					(llvm::Ty::Int{bits: 1, signed: false}, llvm::Operand::Const(llvm::Constant::UInt{bits: 1, val: 0}))
				]
			}));
			context.locals.insert(arg_name.to_string(), (llvm::Ty::Dynamic(arg_ty), llvm::Operand::Local(dst_copy_uid)) );
			params.push( (i8_ptr, ll_arg_id) )
		} else {
			let alloca_slot_id = gensym("arg_slot");
			let ll_ty = cmp_ty(arg_ty, &prog_context.structs, context.current_src_type_param(), context.mode, context.struct_inst_queue, typecache);
			let ll_arg_id = gensym("arg");
			context.stream.push(Component::Instr(alloca_slot_id.clone(), llvm::Instruction::Alloca(ll_ty.clone(), llvm::Operand::Const(llvm::Constant::UInt{bits: 64, val: 1}), None)));
			context.stream.push(Component::Instr(String::new(), llvm::Instruction::Store{
				typ: ll_ty.clone(),
				data: llvm::Operand::Local(ll_arg_id.clone()),
				dest: llvm::Operand::Local(alloca_slot_id.clone())
			}));
			context.locals.insert(arg_name.to_string(), (ll_ty.clone(), llvm::Operand::Local(alloca_slot_id)));
			params.push( (ll_ty, ll_arg_id) );
		}
	}
	if ret_is_dst {
		//the DST return location does not get moved from a local to a stack slot because it will never
		//be modified like normal function parameters. It also is not added to the context.
		params.push( (llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false})), RET_LOC_NAME.to_owned()) );
	}
	if let FuncInst::Erased(_) = f {
		//like the DST return location, the type param size is never modified, so it is not put into
		//a stack slot, and is not inserted into the context.
		params.push( (llvm::Ty::Int{bits: 64, signed: false}, PARAM_SIZE_NAME.to_owned()) );
	}
	//if the function body is empty, I still need to add a 'ret void' terminator
	if !body.0.is_empty() {
		cmp_block(body, &mut context, &ll_ret_ty)
	} else {
		context.stream.push(Component::Term(llvm::Terminator::Ret(None)));
	};
	//if the last statement is a Return, then there will be a Label(unreachable) after it, which needs to be removed
	if matches!(context.stream.last(), Some(Component::Label(_))) {
		context.stream.pop();
	}
	if !matches!(context.stream.last(), Some(Component::Term(_))) {
		debug_assert!(ret_ty.as_ref() == None, "last component of stream is not a terminator in function that does not return void");
		context.stream.push(Component::Term(llvm::Terminator::Ret(None)));
	}
	//convert stream + body_stream to Cfg
	let mut cfg = llvm::Cfg{
		entry: Default::default(),
		other_blocks: Vec::new()
	};
	//let mut current_block: Option<(&str, llvm::Block)> = Some("", Vec::new());
	//if GlobalString(ident, GString("abc")) appears in the stream,
	//the Program.global_decls needs to have (ident, GString("abc") appended to it.
	let mut additional_gdecls = Vec::new();
	let mut seen_first_term = false;
	for component in context.stream.into_iter() { match component {
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
		FuncInst::Separated(_, ty, _) => mangle(func_name, ty)
	};
	let func_result = llvm::Func{
		ret_ty: ll_ret_ty,
		params,
		cfg,
		name: possibly_mangled_name
	};
	(func_result, additional_gdecls)
}

type LLStructContext<'src, 'arena> = HashMap<String, Vec<llvm::Ty<'src, 'arena>>>;

fn get_default_constant<'src: 'arena, 'arena>(ll_ty: &llvm::Ty<'src, 'arena>, structs: &LLStructContext<'src, 'arena>) -> llvm::Constant<'src, 'arena> {
	use llvm::Ty::*;
	match ll_ty {
		Int{bits, ..} => llvm::Constant::SInt{bits: *bits, val: 0},
		Float32 => llvm::Constant::Float32(0.0),
		Float64 => llvm::Constant::Float64(0.0),
		Ptr(_) => llvm::Constant::Null(llvm::Ty::Int{bits: 8, signed: false}),
		Array{length, typ} => llvm::Constant::Array{
			typ: (typ as &llvm::Ty).clone(),
			elements: std::iter::once(get_default_constant(typ, structs)).cycle().take(*length).collect()
		},
		NamedStruct(llvm_name, _src_name, _type_param_opt) => llvm::Constant::Struct{
			name: llvm_name.clone(),
			values: structs.get(llvm_name).expect("types of global vars should be insted by now")
				.iter()
				.map(|t| get_default_constant(t, structs))
				.collect()
		},
		Void => panic!("global cannot have void type"),
		Dynamic(t) => panic!("global vars cannot be dynamically sized, like {}", t),
	}
}

fn cmp_global_var<'src: 'arena, 'arena>(
		typ: &'arena ast2::Ty<'src, 'arena>,
		structs: &'arena typechecker::StructContext<'src, 'arena>,
		type_decls: &mut LLStructContext<'src, 'arena>,
		struct_inst_queue: &Mutex<SeparatedStructInstQueue<'src, 'arena>>,
		typecache: &'arena ast2::TypeCache<'src, 'arena>
		) -> (llvm::Ty<'src, 'arena>, llvm::GlobalDecl<'src, 'arena>) {
	let ll_ty = cmp_ty(typ, structs, None, None, struct_inst_queue, typecache);
	//if any structs were added to the struct queue, they need to be compiled and added to ll_structs so that get_default_constant can see them
	while let Some(SeparatedStructInst{name, type_param}) = {let mut guard = struct_inst_queue.lock().unwrap(); let result = (*guard).poll(); drop(guard); result} {
		let fields = match structs.get(name.as_str()).unwrap() {
			typechecker::StructType::Generic{mode: ast2::PolymorphMode::Separated, fields, ..} => fields,
			_ => panic!("found non-separated struct when looking up '{}' in struct context", name)
		};
		let cmped_tys = fields.iter().map(|(_, t)| cmp_ty(t, structs, Some(type_param), Some(ast2::PolymorphMode::Separated), struct_inst_queue, typecache)).collect();
		let mangled_name = mangle(name.as_str(), type_param);
		type_decls.insert(mangled_name, cmped_tys);
	}
	let initializer: llvm::Constant<'_, '_> = get_default_constant(&ll_ty, type_decls);
	(ll_ty.clone(), llvm::GlobalDecl::GConst(ll_ty, initializer))
}

fn cmp_external_decl<'src: 'arena, 'arena>(
		e: &ast2::ExternalFunc<'src, 'arena>, 
		structs: &typechecker::StructContext<'src, 'arena>,
		typecache: &'arena ast2::TypeCache<'src, 'arena>
		) -> (String, llvm::Ty<'src, 'arena>, Vec<llvm::Ty<'src, 'arena>>) {
	let dummy_struct_queue = SeparatedStructInstQueue::new();
	let mutex = Mutex::new(dummy_struct_queue);
	(
		e.name.to_string(),
		e.ret_type.as_ref().map(|t| cmp_ty(t, structs, None, None, &mutex, typecache)).unwrap_or(llvm::Ty::Void),
		e.arg_types.iter().map(|t| cmp_ty(t, structs, None, None, &mutex, typecache)).collect()
	)
}

//when insting this, replace all occurences of its type var in fields with type_param
#[derive(Debug)]
struct SeparatedStructInst<'src: 'arena, 'arena>{
	name: String,
	type_param: &'arena ast2::Ty<'src, 'arena>
}

#[derive(Debug)]
struct SeparatedStructInstQueue<'src: 'arena, 'arena>{
	queue: VecDeque<SeparatedStructInst<'src, 'arena>>,
	already_insted: HashSet<(String, &'arena ast2::Ty<'src, 'arena>)>
}
impl<'src: 'arena, 'arena> SeparatedStructInstQueue<'src, 'arena>{
	fn new() -> Self {
		Self{
			queue: VecDeque::new(),
			already_insted: HashSet::new(),
		}
	}

	fn push(&mut self, struct_name: String, type_param: &'arena ast2::Ty<'src, 'arena>) -> bool {
		let tuple = (struct_name, type_param);
		if self.already_insted.contains(&tuple){
			false
		} else {
			let (struct_name, type_param) = tuple;
			self.queue.push_back(SeparatedStructInst{
				name: struct_name.clone(),
				type_param
			});
			self.already_insted.insert((struct_name, type_param));
			true
		}
	}
	fn poll(&mut self) -> Option<SeparatedStructInst<'src, 'arena>>{
		self.queue.pop_front()
	}
}

//structs are already checked for unlimited instantiations, but functions are not
//SeparatedFuncInst needs to have a depth field, which increases with every recursive instantiation
#[derive(Debug)]
struct SeparatedFuncInst<'src: 'arena, 'arena>{
	name: String,
	type_param: &'arena ast2::Ty<'src, 'arena>,
	depth: u8
}

#[derive(Debug)]
struct SeparatedFuncInstQueue<'src: 'arena, 'arena>{
	queue: VecDeque<SeparatedFuncInst<'src, 'arena>>,
	already_insted: HashSet<(String, &'arena ast2::Ty<'src, 'arena>)>
}
impl<'src: 'arena, 'arena> SeparatedFuncInstQueue<'src, 'arena>{
	fn new() -> Self {
		Self {
			queue: VecDeque::new(),
			already_insted: HashSet::new()
		}
	}

	//caller of this function must add 1 to depth
	fn push(&mut self, func_name: String, type_param: &'arena ast2::Ty<'src, 'arena>, depth: u8) -> bool {
		let tuple = (func_name, type_param);
		if self.already_insted.contains(&tuple){
			false
		} else {
			let (func_name, type_param) = tuple;
			self.queue.push_back(SeparatedFuncInst{
				name: func_name.clone(),
				type_param,
				depth
			});
			self.already_insted.insert((func_name, type_param));
			true
		}
	}
	#[allow(dead_code)]
	fn poll(&mut self) -> Option<SeparatedFuncInst<'src, 'arena>>{
		self.queue.pop_front()
	}

}

pub fn cmp_prog<'src: 'arena, 'arena>(
		//prog should really be borrowed for 'arena, but making this 'src fixes strange errors...
		prog: &'src ast2::Program<'src, 'arena>,
		prog_context: &'arena typechecker::ProgramContext<'src, 'arena>,
		target_triple: &'arena str,
		errno_func_name: &'arena str,
		typecache: &'arena ast2::TypeCache<'src, 'arena>
		) -> llvm::Program<'src, 'arena> {
	let mut type_decls: LLStructContext = HashMap::new();
	let mut struct_inst_queue: Mutex<SeparatedStructInstQueue> = Mutex::new(SeparatedStructInstQueue::new());
	let mut func_inst_queue: Mutex<SeparatedFuncInstQueue> = Mutex::new(SeparatedFuncInstQueue::new());
	//initially, put all non-generic structs in the type_decls
	for s in prog.structs.iter() {
		//any structs that are dynamically sized do not get declared, llvm does not know about them
		if s.fields.iter().any(|(t, _)| t.is_DST(&prog_context.structs, None, typecache)) {continue}
		let cmped_tys = s.fields.iter().map(|(t, _)| cmp_ty(t, &prog_context.structs, None, None, &struct_inst_queue, typecache)).collect();
		type_decls.insert(s.name.to_string(), cmped_tys);
	}
	//erased structs do not get declared, llvm does not know about them
	//they don't need to be in `type_decls`, because globals vars cannot be DSTs

	let mut global_decls: Vec<(String, llvm::GlobalDecl<'_, '_>)> = Vec::with_capacity(prog.global_vars.len());
	let mut global_locs: HashMap<String, (llvm::Ty<'_, '_>, llvm::Operand<'_, '_>)> = HashMap::new();
	for (typ, name) in prog.global_vars.iter() {
		let (ll_typ, ll_gdecl) = cmp_global_var(typ, &prog_context.structs, &mut type_decls, &struct_inst_queue, typecache);
		global_decls.push( (name.to_string(), ll_gdecl) );
		global_locs.insert(name.to_string(), (ll_typ, llvm::Operand::Global(name.to_string())));
	}
	let mut cmped_funcs: Vec<llvm::Func<'_, '_>> = Vec::new();
	let cmped_funcs_and_extra_globals: Vec<(llvm::Func<'src, 'arena>, Vec<(String, llvm::GlobalDecl<'src, 'arena>)>)> = prog.funcs.par_iter().map(|func| {
		cmp_func(FuncInst::NonGeneric(func), prog_context, &global_locs, &struct_inst_queue, &func_inst_queue, errno_func_name, typecache)
	}).collect();
	for (cmped_func, extra_globals) in cmped_funcs_and_extra_globals.into_iter() {
		cmped_funcs.push(cmped_func);
		global_decls.extend(extra_globals.into_iter());
	}
	let cmped_erased_funcs_and_extra_globals: Vec<(llvm::Func<'_, '_>, Vec<(String, llvm::GlobalDecl<'_, '_>)>)> = prog.erased_funcs.par_iter().map(|func| {
		cmp_func(FuncInst::Erased(func), prog_context, &global_locs, &struct_inst_queue, &func_inst_queue, errno_func_name, typecache)
	}).collect();
	for (cmped_func, extra_globals) in cmped_erased_funcs_and_extra_globals.into_iter() {
		cmped_funcs.push(cmped_func);
		global_decls.extend(extra_globals.into_iter());
	}
	//compiling the non-generic funcs and erased funcs will put things in both inst queues, now iterate over those until they are empty
	//insting a struct will never cause a func inst, so iterate over the func inst queue first, then the struct inst queue
	loop {
		let queue_entries: Vec<SeparatedFuncInst<'_, '_>> = func_inst_queue.get_mut().unwrap().queue.drain(..).collect();
		if queue_entries.is_empty() {break}
		let cmped_funcs_and_global_decls: Vec<(llvm::Func<'_, '_>, Vec<(String, llvm::GlobalDecl<'_, '_>)>)> = queue_entries.par_iter().map(|SeparatedFuncInst{name, type_param, depth}| {
			if *depth > SEPARATED_FUNC_MAX_DEPTH {
				panic!("reached the maximum separated function instantiation depth when processing function {}@<{:?}>", name, type_param);
			}
			//I only know the name of the function, so I have to iterate over the all the separated functions to find the one with this name
			let func: &ast2::GenericFunc<'_, '_> = prog.separated_funcs.iter().find(|gfunc: &&ast2::GenericFunc<'_, '_>| gfunc.name.elt == name).unwrap();
			cmp_func(FuncInst::Separated(func, type_param, *depth), prog_context, &global_locs, &struct_inst_queue, &func_inst_queue, errno_func_name, typecache)
		}).collect();
		for (cmped_func, extra_globals) in cmped_funcs_and_global_decls.into_iter() {
			cmped_funcs.push(cmped_func);
			global_decls.extend(extra_globals.into_iter());
		}
		
	}
	loop {
		let queue_entries: Vec<SeparatedStructInst<'src, 'arena>> = struct_inst_queue.get_mut().unwrap().queue.drain(..).collect();
		if queue_entries.is_empty() {break}
		let names_and_cmped_tys: Vec<(String, Vec<llvm::Ty<'_, '_>>)> = queue_entries.into_par_iter().map(|SeparatedStructInst{name, type_param}| {
			//separated structs containing DSTs should never be added to the struct queue
			debug_assert!(
				!ast2::Ty::is_DST(
					&ast2::Ty::GenericStruct{name: Box::leak(name.clone().into_boxed_str()), type_param},
					&prog_context.structs,
					Some(ast2::PolymorphMode::Separated),
					typecache
				),
				"struct queue contains {{ name: '{}', type_param: {:?} }}, which is a DST", &name, &type_param);
			let fields = match prog_context.structs.get(name.as_str()).unwrap() {
				typechecker::StructType::Generic{mode: ast2::PolymorphMode::Separated, fields, ..} => fields,
				_ => panic!("found non-separated struct when looking up '{}' in struct context", name)
			};
			let cmped_tys = fields.iter().map(|(_, t)| cmp_ty(t, &prog_context.structs, Some(type_param), Some(ast2::PolymorphMode::Separated), &struct_inst_queue, typecache)).collect();
			let mangled_name = mangle(name.as_str(), type_param);
			(mangled_name, cmped_tys)
			//type_decls.insert(mangle(name.as_str(), &type_param), cmped_tys);
		}).collect();
		type_decls.extend(names_and_cmped_tys.into_iter());
	}
	let mut seen_external_decls = HashSet::new();
	let mut external_decls = Vec::new();
	for external_func in prog.external_funcs.iter() {
		if !seen_external_decls.contains(external_func.name.elt) {
			seen_external_decls.insert(external_func.name.elt);
			external_decls.push(cmp_external_decl(external_func, &prog_context.structs, typecache));
		}
	}
	external_decls.push( (errno_func_name.to_owned(), llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 32, signed: true})), vec![]) );
	llvm::Program {
		type_decls,
		global_decls,
		func_decls: cmped_funcs,
		external_decls,
		target_triple: target_triple.to_owned()
	}
}
