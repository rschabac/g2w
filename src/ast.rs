#[derive(Debug, PartialEq, Clone, PartialOrd, Copy, Eq, Hash)]
pub enum IntSize{
	Size8,
	Size16,
	Size32,
	Size64
}
impl std::fmt::Display for IntSize {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use IntSize::*;
		write!(f, "{}", 
			match self {
				Size8 => 8,
				Size16 => 16,
				Size32 => 32,
				Size64 => 64
			}
		)
	}
}

#[derive(Debug, PartialEq, Clone, PartialOrd, Copy, Eq, Hash)]
pub enum FloatSize{
	FSize32,
	FSize64
}
impl std::fmt::Display for FloatSize {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use FloatSize::*;
		write!(f, "{}", 
			match self {
				FSize32 => 32,
				FSize64 => 64
			}
		)
	}
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum Ty{
	Bool,
	Int{signed: bool, size: IntSize},
	Float(FloatSize),
	Ptr(Option<Box<Ty>>),	//void pointers are represented as Ptr(None)
	Array{length: u64, typ: Box<Ty>},
	Struct(String),
	TypeVar(String),
	GenericStruct{type_var: Box<Ty>, name: String},
}
impl std::fmt::Display for Ty {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use Ty::*;
		match self {
			Bool => write!(f, "bool"),
			Int{signed: true, size} => write!(f, "i{}", size),
			Int{signed: false, size} => write!(f, "u{}", size),
			Float(size) => write!(f, "f{}", size),
			Ptr(None) => write!(f, "void*"),
			Ptr(Some(t)) => write!(f, "{}*", t),
			Array{length, typ} => write!(f, "{}[{}]", typ, length),
			Struct(s) => write!(f, "struct {}", s),
			TypeVar(s) => write!(f, "'{}", s),
			GenericStruct{type_var, name} => write!(f, "struct {} @<{}>", name, type_var)
		}
	}
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum UnaryOp{
	Neg, Lognot, Bitnot
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BinaryOp{
	Add, Sub, Mul, Div, Mod,
	Equ, Neq,
	Lt, Lte, Gt, Gte,
	And, Or,
	Bitand, Bitor, Bitxor,
	Shl /* << */, Shr /* >> */, Sar	/* >>> */
}

#[derive(Debug, PartialEq)]
pub enum Expr{
	LitNull,
	LitBool(bool),
	//For the time being, all integer literals will be 64 bits
	LitSignedInt(i64),
	LitUnsignedInt(u64),
	LitFloat(f64),
	LitString(String),
	Id(String),
	//Type of an array literal will be inferred based on the first element
	LitArr(Vec<Expr>),
	Index(Box<Expr>, Box<Expr>),
	//maybe add this back in later
	//LitStruct{struct_name: String, values: Vec<(String, Expr)>},
	Proj(Box<Expr>, String),
	Call(String, Vec<Expr>),
	GenericCall{name: String, type_var: Ty, args: Vec<Expr>},
	Cast(Ty, Box<Expr>),
	Binop(Box<Expr>, BinaryOp, Box<Expr>),
	Unop(UnaryOp, Box<Expr>),
	GetRef(Box<Expr>),
	Deref(Box<Expr>),
	Sizeof(Ty)
}

#[derive(Debug, PartialEq)]
pub enum Stmt{
	Assign(Expr, Expr),
	Decl(Ty, String),
	Return(Option<Expr>),
	SCall(String, Vec<Expr>),
	GenericSCall{name: String, type_var: Ty, args: Vec<Expr>},
	If(Expr, Block, Block),
	While(Expr, Block)
}

pub type Block = Vec<Stmt>;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum PolymorphMode{
	Separated,
	Erased
}

#[derive(Debug, PartialEq)]
pub enum Gdecl{
	GVarDecl(Ty, String),
	GFuncDecl{ret_type: Option<Ty>, name: String, args: Vec<(Ty, String)>, body: Block},
	GStructDecl{name: String, fields: Vec<(Ty, String)>},
	GGenericStructDecl{name: String, param: String, mode: PolymorphMode, fields: Vec<(Ty, String)>},
	GGenericFuncDecl{name: String, ret_type: Option<Ty>, args: Vec<(Ty, String)>, body: Block, param: String, mode: PolymorphMode}
}
