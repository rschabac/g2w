//These types should reflect https://docs.rs/llvm-ir/0.7.4/llvm_ir/
#![allow(dead_code)]

#[derive(Clone, Debug, PartialEq)]
pub enum Ty{
	//Void,
	//Bool,
	Int{bits: u32, signed: bool},
	Float32,
	Float64,
	Ptr(Box<Ty>),
	//shouldn't need function types because there are no function pointers
	//Func{result: Box<Ty>, param_types: Vec<Ty>, is_var_arg: bool},
	Array{length: usize, typ: Box<Ty>},
	NamedStruct(String),
}

pub enum Terminator{
	Ret(Option<Operand>),
	Br(String),
	CondBr{condition: Operand, true_dest: String, false_dest: String},
}

#[derive(Clone)]
pub enum Operand{
	Const(Constant),
	Local(String),
	Global(String),
	Array{typ: Ty, elements: Vec<Operand>}
}

#[derive(Clone)]
pub enum Constant{
	SInt{bits: u32, val: i64},
	UInt{bits: u32, val: u64},
	Float32(f32),
	Float64(f64),
	Null(Ty),
	Struct{name: String, values: Vec<Constant>},
	Array{typ: Ty, elements: Vec<Constant>},
	//The llvm_ir crate includes variants here to support constant expressions, I am omitting these
}

pub enum BinaryOp{
	Add, Sub, Mul, Div, Mod,
	And, Or,
	Bitand, Bitor, Bitxor,
	Shl, Shr, Sar
}

pub enum Cond{
	Equ, Neq,
	Lt, Lte,
	Gt, Gte
}

//Instructions do not include the local they are assigned to
pub enum Instruction{
	Binop{op: BinaryOp, typ: Ty, left: Operand, right: Operand},
	Alloca(Ty),
	Load{typ: Ty, src: Operand},
	Store{typ: Ty, data: Operand, dest: Operand},
	Cmp{cond: Cond, typ: Ty, left: Operand, right: Operand},
	Call{func_name: String, ret_typ: Ty, args: Vec<(Ty, Operand)>},
	Bitcast{original_typ: Ty, op: Operand, new_typ: Ty},
	Gep{typ: Ty, base: Operand, offsets: Vec<Operand>},
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

pub struct Block{
	pub insns: Vec<(String, Instruction)>,
	pub term: Terminator
}

pub struct CFG{
	pub entry: Block,
	pub other_blocks: Vec<(String, Block)>,
}

pub struct Func{
	pub ret_ty: Ty,
	pub params: Vec<(Ty, String)>,
	pub cfg: CFG
}

pub enum GlobalInit{
	GString(String),
	GBitcast{original_typ: Ty, expr: Box<GlobalInit>, new_typ: Ty},
	GConst(Constant),
	GGid(String),
}

pub struct GlobalDecl{
	pub typ: Ty,
	pub init: GlobalInit
}

pub struct Program{
	pub type_decls: Vec<(String, Ty)>,
	pub global_decls: Vec<(String, GlobalDecl)>,
	pub func_decls: Vec<(String, Func)>,
	pub external_decls: Vec<(String, Ty)>
}

//to_string functions will go here later
