//These types should reflect https://docs.rs/llvm-ir/0.7.4/llvm_ir/

use crate::typechecker;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Ty<'src: 'arena, 'arena>{
	Void,
	Int{bits: u32, signed: bool},
	Float32,
	Float64,
	Ptr(Box<Ty<'src, 'arena>>),
	//shouldn't need function types because there are no function pointers
	//Func{result: Box<Ty>, param_types: Vec<Ty>, is_var_arg: bool},
	Array{length: usize, typ: Box<Ty<'src, 'arena>>},
	//contains the llvm struct name (which may be mangled), and the source struct name and type param
	NamedStruct(String, String, Option<&'arena super::ast2::Ty<'src, 'arena>>),
	
	//a type that is dynamically sized is either an erased struct, a struct (of any kind) that
	//contains a DST, or an array of DSTs
	Dynamic(&'arena super::ast2::Ty<'src, 'arena>)
}
impl<'src: 'arena, 'arena> Ty<'src, 'arena> {
	pub fn remove_ptr(self) -> Self {
		match self {
			Ty::Ptr(t) => *t,
			other => panic!("Cannot remove_ptr of type {:?}", other)
		}
	}
}
impl<'src: 'arena, 'arena> std::fmt::Display for Ty<'src, 'arena>{
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

pub enum Terminator<'src: 'arena, 'arena>{
	Ret(Option<(Ty<'src, 'arena>, Operand<'src, 'arena>)>),
	Br(String),
	CondBr{condition: Operand<'src, 'arena>, true_dest: String, false_dest: String},
}
impl<'src: 'arena, 'arena> std::fmt::Display for Terminator<'src, 'arena>{
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
pub enum Operand<'src: 'arena, 'arena>{
	Const(Constant<'src, 'arena>),
	Local(String),
	Global(String),
}
impl<'src: 'arena, 'arena> std::fmt::Display for Operand<'src, 'arena>{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Operand::*;
		match self {
			Const(c) => write!(f, "{}", c),
			Local(s) => write!(f, "%{}", s),
			Global(s) => write!(f, "@{}", s),
		}
	}
}

#[derive(Clone)]
pub enum Constant<'src: 'arena, 'arena>{
	SInt{bits: u32, val: i64},
	UInt{bits: u32, val: u64},
	Float32(f64),
	Float64(f64),
	Null(Ty<'src, 'arena>),
	Struct{name: String, values: Vec<Constant<'src, 'arena>>},
	Array{typ: Ty<'src, 'arena>, elements: Vec<Constant<'src, 'arena>>},
	//The llvm_ir crate includes variants here to support constant expressions, I am omitting these
}
impl<'src: 'arena, 'arena> Constant<'src, 'arena> {
	fn print_type(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Constant::*;
		match self {
			SInt{bits, ..} | UInt{bits, ..} => write!(f, "i{}", bits),
			Float32(_) => write!(f, "float"),
			Float64(_) => write!(f, "double"),
			Null(t) => write!(f, "{}*", t),
			Struct{name, ..} => write!(f, "%{}", name),
			Array{typ, elements} => write!(f, "[{} x {}]", elements.len(), typ)
		}
	}
}
impl<'src: 'arena, 'arena> std::fmt::Display for Constant<'src, 'arena>{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Constant::*;
		match self {
			SInt{val, ..} => write!(f, "{}", val),
			UInt{val, ..} => write!(f, "{}", val),
			Float32(val) => write!(f, "{}{}", val, if val.fract() == 0.0 {".0"} else {""}),
			Float64(val) => write!(f, "{}{}", val, if val.fract() == 0.0 {".0"} else {""}),
			Null(_) => write!(f, "null"),
			Struct{values, ..} => {
				write!(f, "{{")?;
				if !values.is_empty() {
					values[0].print_type(f)?;
					write!(f, " {}", values[0])?;
					for constant in values[1..].iter() {
						write!(f, ", ")?;
						constant.print_type(f)?;
						write!(f, " {}", constant)?;
					}
				}
				write!(f, " }}")
			},
			Array{elements, ..} => {
				write!(f, "[")?;
				if !elements.is_empty() {
					elements[0].print_type(f)?;
					write!(f, " {}", elements[0])?;
					for constant in elements[1..].iter() {
						write!(f, ", ")?;
						constant.print_type(f)?;
						write!(f, " {}", constant)?;
					}
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
pub enum Instruction<'src: 'arena, 'arena>{
	Binop{op: BinaryOp, typ: Ty<'src, 'arena>, left: Operand<'src, 'arena>, right: Operand<'src, 'arena>},
	Alloca(Ty<'src, 'arena>, Operand<'src, 'arena>, Option<u64>),
	Load{typ: Ty<'src, 'arena>, src: Operand<'src, 'arena>},
	Store{typ: Ty<'src, 'arena>, data: Operand<'src, 'arena>, dest: Operand<'src, 'arena>},
	Cmp{cond: Cond, typ: Ty<'src, 'arena>, left: Operand<'src, 'arena>, right: Operand<'src, 'arena>},
	Call{func_name: String, ret_typ: Ty<'src, 'arena>, args: Vec<(Ty<'src, 'arena>, Operand<'src, 'arena>)>},
	Bitcast{original_typ: Ty<'src, 'arena>, op: Operand<'src, 'arena>, new_typ: Ty<'src, 'arena>},
	Gep{typ: Ty<'src, 'arena>, base: Operand<'src, 'arena>, offsets: Vec<(Ty<'src, 'arena>, Operand<'src, 'arena>)>},
	Extract{typ: Ty<'src, 'arena>, base: Operand<'src, 'arena>, offset: u64}, //needed for projecting off of structs (maybe)
	//will likely need to add more Instruction variants for floating point, etc.
	Trunc{old_bits: u32, op: Operand<'src, 'arena>, new_bits: u32},
	Ext{old_bits: u32, op: Operand<'src, 'arena>, new_bits: u32, signed: bool},
	//I only truncate floats from 64 bits to 32 bits, and only extend floats from 32 bits to 64 bits,
	//so only the operand is needed.
	FloatTrunc(Operand<'src, 'arena>),
	FloatExt(Operand<'src, 'arena>),
	SignedToFloat{old_bits: u32, op: Operand<'src, 'arena>, result_is_64_bit: bool},
	UnsignedToFloat{old_bits: u32, op: Operand<'src, 'arena>, result_is_64_bit: bool},
	FloatToSigned{src_is_64_bit: bool, op: Operand<'src, 'arena>, new_bits: u32},
	FloatToUnsigned{src_is_64_bit: bool, op: Operand<'src, 'arena>, new_bits: u32},
	FloatNeg{is_64_bit: bool, op: Operand<'src, 'arena>},
	PtrToInt{ptr_ty: Ty<'src, 'arena>, op: Operand<'src, 'arena>}, //size of the resulting integer will always be 64 bits
}
impl<'src: 'arena, 'arena> std::fmt::Display for Instruction<'src, 'arena>{
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
				match func_name.as_str() {
					"printf" => write!(f, "(i8*, ...) ")?,
					"sprintf" => write!(f, "(i8*, i8*, ...) ")?,
					"snprintf" => write!(f, "(i8*, i64, i8*, ...) ")?,
					"dprintf" => write!(f, "(i32, i8*, ...) ")?,
					other => debug_assert!(!typechecker::PRINTF_FAMILY.contains(&other), "need to add special case in llvm::Instruction Display for printf-like function {}", other)
				};
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

pub struct Block<'src: 'arena, 'arena>{
	pub insns: Vec<(String, Instruction<'src, 'arena>)>,
	pub term: Terminator<'src, 'arena>
}
impl<'src: 'arena, 'arena> std::fmt::Display for Block<'src, 'arena> {
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
impl<'src: 'arena, 'arena> Default for Block<'src, 'arena> {
	fn default() -> Self {
		Self{
			insns: Vec::new(),
			term: Terminator::Br("$$$_Default_Term_$$$".to_owned())
		}
	}
}

pub struct Cfg<'src: 'arena, 'arena>{
	pub entry: Block<'src, 'arena>,
	pub other_blocks: Vec<(String, Block<'src, 'arena>)>,
}
impl<'src: 'arena, 'arena> std::fmt::Display for Cfg<'src, 'arena>{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.entry)?;
		for (label, block) in self.other_blocks.iter() {
			write!(f, "{}:\n{}", label, block)?;
		}
		Ok(())
	}
}

pub struct Func<'src: 'arena, 'arena>{
	pub ret_ty: Ty<'src, 'arena>,
	pub params: Vec<(Ty<'src, 'arena>, String)>,
	pub cfg: Cfg<'src, 'arena>,
	pub name: String
}
impl<'src: 'arena, 'arena> std::fmt::Display for Func<'src, 'arena>{
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

pub enum GlobalDecl<'src: 'arena, 'arena>{
	GString(String),
	//GBitcast{original_typ: Ty, expr: Box<GlobalDecl>, new_typ: Ty},
	GConst(Ty<'src, 'arena>, Constant<'src, 'arena>),
	//GGid(Ty, String),
}
impl<'src: 'arena, 'arena> std::fmt::Display for GlobalDecl<'src, 'arena>{
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
pub struct Program<'src: 'arena, 'arena>{
	pub type_decls: HashMap<String, Vec<Ty<'src, 'arena>>>,
	pub global_decls: Vec<(String, GlobalDecl<'src, 'arena>)>,
	pub func_decls: Vec<Func<'src, 'arena>>,
	pub external_decls: Vec<(String, Ty<'src, 'arena>, Vec<Ty<'src, 'arena>>)>,
	pub target_triple: String
}
impl<'src: 'arena, 'arena> std::fmt::Display for Program<'src, 'arena> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		writeln!(f, "target triple = \"{}\"", self.target_triple)?;
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
			if matches!(gdecl, GlobalDecl::GString(_)) {
				//writing 'unnamed_addr' before a string allows llvm to merge it with any other string literals in the program
				writeln!(f, "@{} = unnamed_addr constant {}", name, gdecl)?;
			} else {
				writeln!(f, "@{} = global {}", name, gdecl)?;
			}
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
