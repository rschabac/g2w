//These types should reflect https://docs.rs/llvm-ir/0.7.4/llvm_ir/

use crate::typechecker;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Ty{
	Void,
	Int{bits: u32, signed: bool},
	Float32,
	Float64,
	Ptr(Box<Ty>),
	//shouldn't need function types because there are no function pointers
	//Func{result: Box<Ty>, param_types: Vec<Ty>, is_var_arg: bool},
	Array{length: usize, typ: Box<Ty>},
	//contains the llvm struct name (which may be mangled), and the source struct name and type param
	NamedStruct(String, String, Option<super::ast::Ty>),
	
	//a type that is dynamically sized is either an erased struct, a struct (of any kind) that
	//contains a DST, or an array of DSTs
	Dynamic(super::ast::Ty)
}
impl Ty {
	pub fn remove_ptr(self) -> Self {
		match self {
			Ty::Ptr(t) => *t,
			other => panic!("Cannot remove_ptr of type {:?}", other)
		}
	}
}
impl std::fmt::Display for Ty{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Ty::*;
		match self {
			Void => write!(f, "void"),
			Int{bits, ..} => write!(f, "i{}", bits),
			Float32 => write!(f, "float"),
			Float64 => write!(f, "double"),
			Ptr(boxed) => write!(f, "{}*", boxed),
			Array{length, typ} => write!(f, "[{} x {}]", length, typ),
			NamedStruct(s, _, _) => write!(f, "%{}", s),
			Dynamic(_t) => {
				//eprintln!("llvm prog contains Dynamic {}", t);
				//write!(f, "(ERROR: Dynamic {})", t)
				write!(f, "i8")
			},
		}
	}
}

pub enum Terminator{
	Ret(Option<(Ty, Operand)>),
	Br(String),
	CondBr{condition: Operand, true_dest: String, false_dest: String},
}
impl std::fmt::Display for Terminator{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Terminator::*;
		match self {
			Ret(None) => write!(f, "ret void"),
			Ret(Some((typ, op))) => write!(f, "ret {} {}", typ, op),
			Br(s) => write!(f, "br label %{}", s),
			CondBr{condition, true_dest, false_dest} => write!(f, "br i1 {}, label %{}, label %{}", condition, true_dest, false_dest),
		}
	}
}

#[derive(Clone)]
pub enum Operand{
	Const(Constant),
	Local(String),
	Global(String),
	Array{typ: Ty, elements: Vec<Operand>}
}
impl std::fmt::Display for Operand{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Operand::*;
		match self {
			Const(c) => write!(f, "{}", c),
			Local(s) => write!(f, "%{}", s),
			Global(s) => write!(f, "@{}", s),
			Array{elements, ..} => {
				write!(f, "[")?;
				for element in elements.iter(){
					write!(f, " {},", element)?;
				}
				write!(f, " ]")
			}
		}
	}
}

#[derive(Clone)]
pub enum Constant{
	SInt{bits: u32, val: i64},
	UInt{bits: u32, val: u64},
	//currently, all constants are 64-bit, so there is no need for 32-bit float constants
	//Float32(f32),
	Float64(f64),
	Null(Ty),
	Struct{name: String, values: Vec<Constant>},
	Array{typ: Ty, elements: Vec<Constant>},
	//The llvm_ir crate includes variants here to support constant expressions, I am omitting these
}
impl std::fmt::Display for Constant{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Constant::*;
		match self {
			SInt{val, ..} => write!(f, "{}", val),
			UInt{val, ..} => write!(f, "{}", val),
			//Float32(val) => write!(f, "{}{}", val, if val.fract() == 0.0 {".0"} else {""}),
			Float64(val) => write!(f, "{}{}", val, if val.fract() == 0.0 {".0"} else {""}),
			Null(_) => write!(f, "null"),
			Struct{values, ..} => {
				write!(f, "{{")?;
				for constant in values.iter() {
					write!(f, " {},", constant)?;
				}
				write!(f, " }}")
			},
			Array{elements, ..} => {
				write!(f, "[")?;
				for element in elements.iter(){
					write!(f, " {},", element)?;
				}
				write!(f, " ]")
			}
		}
	}
}

pub enum BinaryOp{
	Add, Sub, Mul, Div, Mod,
	And, Or,
	Bitand, Bitor, Bitxor,
	Shl, Shr, Sar
}
impl std::fmt::Display for BinaryOp{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use BinaryOp::*;
		match self {
			Add => write!(f, "add"),
			Sub => write!(f, "sub"),
			Mul => write!(f, "mul"),
			Div => panic!("should handle Div in instruction, need signedness"),
			Mod => panic!("should handle Mod in instruction, need signedness"),
			And => write!(f, "and"),
			Or => write!(f, "or"),
			Bitand => write!(f, "and"),
			Bitor => write!(f, "or"),
			Bitxor => write!(f, "xor"),
			Shl => write!(f, "shl"),
			Shr => write!(f, "shr"),
			Sar => write!(f, "sar"),
		}
	}
}

#[derive(Debug)]
pub enum Cond{
	Equ, Neq,
	Lt, Lte,
	Gt, Gte
}
impl Cond{
	fn format_signed(&self) -> &str {
		use Cond::*;
		match self {
			Equ => "eq",
			Neq => "ne",
			Lt => "slt",
			Lte => "sle",
			Gt => "sgt",
			Gte => "sge"
		}
	}
	fn format_unsigned(&self) -> &str {
		use Cond::*;
		match self {
			Equ => "eq",
			Neq => "ne",
			Lt => "ult",
			Lte => "ule",
			Gt => "ugt",
			Gte => "uge"
		}
	}
	fn format_float(&self) -> &str {
		use Cond::*;
		match self {
			Equ => "oeq",
			Neq => "one",
			Lt => "olt",
			Lte => "ole",
			Gt => "ogt",
			Gte => "oge"
		}
	}
}

//Instructions do not include the local they are assigned to
pub enum Instruction{
	Binop{op: BinaryOp, typ: Ty, left: Operand, right: Operand},
	Alloca(Ty, Operand, Option<u64>),
	Load{typ: Ty, src: Operand},
	Store{typ: Ty, data: Operand, dest: Operand},
	Cmp{cond: Cond, typ: Ty, left: Operand, right: Operand},
	Call{func_name: String, ret_typ: Ty, args: Vec<(Ty, Operand)>},
	Bitcast{original_typ: Ty, op: Operand, new_typ: Ty},
	Gep{typ: Ty, base: Operand, offsets: Vec<(Ty, Operand)>},
	Extract{typ: Ty, base: Operand, offset: u64}, //needed for projecting off of structs (maybe)
	//will likely need to add more Instruction variants for floating point, etc.
	Trunc{old_bits: u32, op: Operand, new_bits: u32},
	Ext{old_bits: u32, op: Operand, new_bits: u32, signed: bool},
	//I only truncate floats from 64 bits to 32 bits, and only extend floats from 32 bits to 64 bits,
	//so only the operand is needed.
	FloatTrunc(Operand),
	FloatExt(Operand),
	SignedToFloat{old_bits: u32, op: Operand, result_is_64_bit: bool},
	UnsignedToFloat{old_bits: u32, op: Operand, result_is_64_bit: bool},
	FloatToSigned{src_is_64_bit: bool, op: Operand, new_bits: u32},
	FloatToUnsigned{src_is_64_bit: bool, op: Operand, new_bits: u32},
	FloatNeg{is_64_bit: bool, op: Operand},
	PtrToInt{ptr_ty: Ty, op: Operand}, //size of the resulting integer will always be 64 bits
}
impl std::fmt::Display for Instruction{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Instruction::*;
		use BinaryOp::*;
		use Ty::*;
		match self {
			Binop{op: Div, typ: Int{bits, signed: true}, left, right} =>
				write!(f, "sdiv i{} {}, {}", bits, left, right),
			Binop{op: Div, typ: Int{bits, signed: false}, left, right} =>
				write!(f, "udiv i{} {}, {}", bits, left, right),
			Binop{op: Div, typ: float_ty @ Float32, left, right} | Binop{op: Div, typ: float_ty @ Float64, left, right} =>
				write!(f, "fdiv {} {}, {}", float_ty, left, right),
			Binop{op: Mod, typ: Int{bits, signed: true}, left, right} =>
				write!(f, "srem i{} {}, {}", bits, left, right),
			Binop{op: Mod, typ: Int{bits, signed: false}, left, right} =>
				write!(f, "urem i{} {}, {}", bits, left, right),
			Binop{op: Mod, typ: float_ty @ Float32, left, right} | Binop{op: Mod, typ: float_ty @ Float64, left, right} =>
				write!(f, "frem {} {}, {}", float_ty, left, right),
			Binop{op, typ: float_ty @ Float32, left, right} | Binop{op, typ: float_ty @ Float64, left, right} =>
				write!(f, "f{} {} {}, {}", op, float_ty, left, right),
			Binop{op, typ, left, right} => write!(f, "{} {} {}, {}", op, typ, left, right),
			Alloca(t, amount, None) => write!(f, "alloca {}, i64 {}", t, amount),
			Alloca(t, amount, Some(alignment)) => write!(f, "alloca {}, i64 {}, align {}", t, amount, alignment),
			Load{typ, src} => write!(f, "load {}, {}* {}", typ, typ, src),
			Store{typ, data, dest} => write!(f, "store {} {}, {}* {}", typ, data, typ, dest),
			Cmp{cond, typ: Int{bits, signed: true}, left, right} => write!(f, "icmp {} i{} {}, {}", cond.format_signed(), bits, left, right),
			Cmp{cond, typ: Int{bits, signed: false}, left, right} => write!(f, "icmp {} i{} {}, {}", cond.format_unsigned(), bits, left, right),
			Cmp{cond, typ: typ @ Ptr(_), left, right} => write!(f, "icmp {} {} {}, {}", cond.format_unsigned(), typ, left, right),
			Cmp{cond, typ: Float32, left, right} => write!(f, "fcmp {} float {}, {}", cond.format_float(), left, right),
			Cmp{cond, typ: Float64, left, right} => write!(f, "fcmp {} double {}, {}", cond.format_float(), left, right),
			Cmp{cond, typ, ..} => panic!("cannot format {:?} cmp of typ {:?}", cond, typ),
			Call{func_name, ret_typ, args} => {
				write!(f, "call {} ", ret_typ)?;
				if typechecker::PRINTF_FAMILY.contains(&func_name.as_str()) {
					write!(f, "(i8*, ...) ")?;
				}
				write!(f, "@{}(", func_name)?;
				for (i, (arg_ty, arg_op)) in args.iter().enumerate() {
					write!(f, "{} {}", arg_ty, arg_op)?;
					if i < args.len() - 1 {
						write!(f, ", ")?;
					}
				}
				write!(f, ")")
			},
			Bitcast{original_typ, op, new_typ} => write!(f, "bitcast {} {} to {}", original_typ, op, new_typ),
			Extract{typ, base, offset} => write!(f, "extractvalue {} {}, {}", typ, base, offset),
			Gep{typ, base, offsets} => {
				write!(f, "getelementptr {}, {}* {}", typ, typ, base)?;
				//write ", {typ} {op} for each op, after figuring out what type the op is
				for (typ, op) in offsets.iter() {
					write!(f, ", {} {}", typ, op)?;
				}
				Ok(())
			},
			Trunc{old_bits, op, new_bits} => write!(f, "trunc i{} {} to i{}", old_bits, op, new_bits),
			Ext{old_bits, op, new_bits, signed} => write!(f, "{}ext i{} {} to i{}", if *signed {'s'}else{'z'}, old_bits, op, new_bits),
			FloatTrunc(op) => write!(f, "fptrunc double {} to float", op),
			FloatExt(op) => write!(f, "fpext float {} to double", op),
			SignedToFloat{old_bits, op, result_is_64_bit} => write!(f, "sitofp i{} {} to {}", old_bits, op, if *result_is_64_bit {"double"} else {"float"}),
			UnsignedToFloat{old_bits, op, result_is_64_bit} => write!(f, "uitofp i{} {} to {}", old_bits, op, if *result_is_64_bit {"double"} else {"float"}),
			FloatToSigned{src_is_64_bit, op, new_bits} => write!(f, "fptosi {} {} to i{}", if *src_is_64_bit {"double"} else {"float"}, op, new_bits),
			FloatToUnsigned{src_is_64_bit, op, new_bits} => write!(f, "fptoui {} {} to i{}", if *src_is_64_bit {"double"} else {"float"}, op, new_bits),
			FloatNeg{is_64_bit, op} => write!(f, "fneg {} {}", if *is_64_bit {"double"} else {"float"}, op),
			PtrToInt{ptr_ty, op} => write!(f, "ptrtoint {} {} to i64", ptr_ty, op)
		}
	}
}

pub struct Block{
	pub insns: Vec<(String, Instruction)>,
	pub term: Terminator
}
impl std::fmt::Display for Block {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		for (local, insn) in self.insns.iter() {
			if matches!(insn, Instruction::Store{..} | Instruction::Call{ret_typ: Ty::Void, ..}) {
				writeln!(f, "\t{}", insn)?;
			} else {
				writeln!(f, "\t%{} = {}", local, insn)?;
			}
		}
		writeln!(f, "\t{}", self.term)
	}
}
impl Default for Block {
	fn default() -> Self {
		Self{
			insns: Vec::new(),
			term: Terminator::Br("$$$_Default_Term_$$$".to_owned())
		}
	}
}

pub struct CFG{
	pub entry: Block,
	pub other_blocks: Vec<(String, Block)>,
}
impl std::fmt::Display for CFG{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.entry)?;
		for (label, block) in self.other_blocks.iter() {
			write!(f, "{}:\n{}", label, block)?;
		}
		Ok(())
	}
}

pub struct Func{
	pub ret_ty: Ty,
	pub params: Vec<(Ty, String)>,
	pub cfg: CFG,
	pub name: String
}
impl std::fmt::Display for Func{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "define {} @{}(", self.ret_ty, self.name)?;
		for (i, (param_ty, param_name)) in self.params.iter().enumerate() {
			write!(f, "{} %{}", param_ty, param_name)?;
			if i < self.params.len() - 1 {
				write!(f, ", ")?;
			}
		}
		writeln!(f, ") {{\n{}}}", self.cfg)
	}
}

pub enum GlobalDecl{
	GString(String),
	//GBitcast{original_typ: Ty, expr: Box<GlobalDecl>, new_typ: Ty},
	GConst(Ty, Constant),
	//GGid(Ty, String),
}
impl std::fmt::Display for GlobalDecl{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use GlobalDecl::*;
		match self {
			GString(s) => write!(f, "[{} x i8] c\"{}\\00\"", 1 + s.len(), s),
			//GBitcast{original_typ, expr, new_typ} => write!(f, "bitcast {} {} to {}", original_typ, expr, new_typ),
			GConst(typ, constant) => write!(f, "{} {}", typ, constant),
			//GGid(typ, name) => write!(f, "{} @{}", typ, name),
		}
	}
}

#[derive(Default)]
pub struct Program{
	pub type_decls: HashMap<String, Vec<Ty>>,
	pub global_decls: Vec<(String, GlobalDecl)>,
	pub func_decls: Vec<Func>,
	pub external_decls: Vec<(String, Ty, Vec<Ty>)>
}
impl std::fmt::Display for Program {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		writeln!(f, "target triple = \"x86_64-unknown-linux\"")?;
		for (name, types) in self.type_decls.iter() {
			write!(f, "%{} = type {{", name)?;
			for (i, ty) in types.iter().enumerate() {
				write!(f, "{}", ty)?;
				if i < types.len() - 1 {
					write!(f, ", ")?;
				}
			}
			writeln!(f, "}}")?;
		}
		for (name, gdecl) in self.global_decls.iter() {
			writeln!(f, "@{} = global {}", name, gdecl)?;
		}
		//llvm's builtin memcpy is not declared automatically
		writeln!(f, "declare void @llvm.memcpy.p0i8.p0i8.i64(i8*, i8*, i64, i1)")?;
		//printf functions have different declaration syntax because of the var args
		writeln!(f, "declare i32 @printf(i8*, ...)\n\
		declare i32 @sprintf(i8*, i8*, ...)\n\
		declare i32 @snprintf(i8*, i64, i8*, ...)\n\
		declare i32 @dprintf(i32, i8*, ...)")?;
		//All external decls will be function
		for (name, ret_ty, arg_tys) in self.external_decls.iter() {
			write!(f, "declare {} @{}(", ret_ty, name)?;
			for (i, ty) in arg_tys.iter().enumerate() {
				write!(f, "{}", ty)?;
				if i < arg_tys.len() - 1 {
					write!(f, ", ")?;
				}
			}
			writeln!(f, ")")?;
		}
		for func in self.func_decls.iter() {
			write!(f, "{}", func)?;
		}
		Ok(())
	}
}
