use crate::ast;
use crate::typechecker;
use crate::llvm;
use std::collections::HashMap;



struct Context<'a>{
	locals: HashMap<String, (llvm::Ty, llvm::Operand)>,
	funcs: &'a typechecker::FuncContext,
}

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
		ast::Ty::Bool => llvm::Ty::Int{bits: 1, signed: false},
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
	ast::Expr::Cast(new_type, src) => {
		let src_result = cmp_exp(src as &ast::Expr, ctxt, &Some(llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))), struct_context);
		let new_llvm_typ = cmp_ty(new_type, struct_context);
		use llvm::Ty::*;
		match (&new_llvm_typ, &src_result.llvm_typ) {
			(Int{bits: new_bits, signed: _new_signed}, Int{bits: old_bits, signed: old_signed}) => {
				if new_bits == old_bits {
					//llvm does not care about the signs
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
						stream: stream
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
						stream: stream
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
					stream: stream
				}
			},
			(Float64, Float32) => {
				let extended_uid = gensym("float_truncated");
				let mut stream = src_result.stream;
				stream.push(Component::Instr(extended_uid.clone(), 
					llvm::Instruction::FloatTrunc(src_result.llvm_op)
				));
				ExpResult{
					llvm_typ: new_llvm_typ,
					llvm_op: llvm::Operand::Local(extended_uid),
					stream: stream
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
					stream: stream
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
					stream: stream
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
					stream: stream
				}
			}
			(new, old) => panic!("trying to cast from {:?} to {:?}", old, new)
		}
	},
	ast::Expr::Binop(left, bop, right) => {
		let left_result = cmp_exp(left, ctxt, &Some(llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))), struct_context);
		let mut right_result = cmp_exp(right, ctxt, &Some(llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))), struct_context);
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
					stream: stream
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
					stream: stream
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
						stream: stream
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
						stream: stream
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
						stream: stream
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
						stream: stream
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
						stream: stream
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
						stream: stream
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
						offset_op
					]
				}));
				ExpResult{
					llvm_typ: left_result.llvm_typ,
					llvm_op: llvm::Operand::Local(ptr_arith_uid),
					stream: stream
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
					stream: stream
				}
			},
			_ => panic!("cannot use binop {:?} on llvm types {:?} and {:?}", bop, left_result.llvm_typ, right_result.llvm_typ)
		}
	},
	ast::Expr::Unop(uop, base) => {
		let base_result = cmp_exp(base, ctxt, &Some(llvm::Ty::Ptr(Box::new(llvm::Ty::Int{bits: 8, signed: false}))), struct_context);
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
					stream: stream
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
					stream: stream
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
					stream: stream
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
					stream: stream
				}
			},
			(Bitnot, t) => panic!("lognot of type {:?}", t)
		}
	},
	ast::Expr::GetRef(boxed) => {
		let mut result = cmp_lvalue(boxed as &ast::Expr, ctxt, struct_context);
		result.llvm_typ = llvm::Ty::Ptr(Box::new(result.llvm_typ));
		result
	},
	ast::Expr::Sizeof(t) => {
		let size_uid = gensym("sizeof");
		let size_int_uid = gensym("sizeof_int");
		let llvm_typ = cmp_ty(t, struct_context);
		let llvm_ptr_typ = llvm::Ty::Ptr(Box::new(llvm_typ.clone()));
		let stream = vec![
			Component::Instr(size_uid.clone(), llvm::Instruction::Gep{
				typ: llvm_ptr_typ.clone(),
				base: llvm::Operand::Const(llvm::Constant::Null(llvm_typ)),
				offsets: vec![llvm::Operand::Const(llvm::Constant::SInt{bits: 32, val: 1})]
			}),
			Component::Instr(size_int_uid.clone(), llvm::Instruction::PtrToInt{
				ptr_ty: llvm_ptr_typ,
				op: llvm::Operand::Local(size_uid)
			})
		];
		ExpResult{
			llvm_typ: llvm::Ty::Int{bits: 64, signed: false},
			llvm_op: llvm::Operand::Local(size_int_uid),
			stream: stream
		}
	},
	ast::Expr::Call(func_name, args) => cmp_call(func_name.clone(), args, ctxt, struct_context),
	ast::Expr::GenericCall{..} => panic!("generic_call not implemented yet")
}}

fn cmp_call(func_name: String, args: &Vec<ast::Expr>, ctxt: &Context, struct_context: &typechecker::StructContext) -> ExpResult {
	//TODO: PRINTF_FAMILY
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
			ast::Expr::LitNull => Some(cmp_ty(expected_ty, struct_context)),
			_ => None
		};
		let mut arg_result = cmp_exp(arg, ctxt, &type_for_lit_nulls, struct_context);
		arg_ty_ops.push((arg_result.llvm_typ, arg_result.llvm_op));
		stream.append(&mut arg_result.stream);
	}
	let uid = gensym("call");
	let llvm_ret_ty = match return_type {
		None => llvm::Ty::Void,
		Some(t) => cmp_ty(t, struct_context)
	};
	stream.push(Component::Instr(uid.clone(), llvm::Instruction::Call{
		func_name: func_name.clone(),
		ret_typ: llvm_ret_ty.clone(),
		args: arg_ty_ops
	}));
	ExpResult{
		llvm_typ: llvm_ret_ty,
		llvm_op: llvm::Operand::Local(uid),
		stream: stream
	}
}

//the op this function returns is a pointer to where the data is stored
//the llvm::Ty this function returns is the type of the thing being pointed to, it may not be a Ptr
fn cmp_lvalue(e: &ast::Expr, ctxt: &Context, struct_context: &typechecker::StructContext) -> ExpResult { match e {
	ast::Expr::Id(s) => {
		let (ll_ty, ll_op) = ctxt.locals.get(s).unwrap_or_else(|| panic!("why is variable {} not in the context?", s));
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
	other => panic!("{:?} is not a valid lvalue", other)
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
