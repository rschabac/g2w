#[derive(Debug, PartialEq)]
pub enum IntSize{
	Size8,
	Size16,
	Size32,
	Size64
}
#[derive(Debug, PartialEq)]
pub enum FloatSize{
	FSize32,
	FSize64
}
#[derive(Debug, PartialEq)]
pub enum Ty{
	Bool,
	Int{signed: bool, size: IntSize},
	Float(FloatSize),
	Ptr(Box<Option<Ty>>),	//void pointers are represented as Ptr(None)
	Struct(String),
	TypeVar(String)
}

#[derive(Debug)]
pub enum UnaryOp{
	Neg,
	Lognot,
	Bitnot
}

#[derive(Debug)]
pub enum BinaryOp{
	Add,
	Sub,
	Mul,
	Div,
	Equ,
	Neq,
	Lt,
	Lte,
	Gt,
	Gte,
	And,
	Or,
	Bitand,
	Bitor,
	Bitxor,
	Shl,
	Shr,
	Sar
}

#[derive(Debug)]
pub enum Expr{
	LitNull,
	LitBool(bool),
	LitInt{signed: bool, size: IntSize},
	LitString(String),
	Id(String),
	LitArr{typ: Ty, values: Vec<Expr>},
	Index(Box<Expr>, Box<Expr>),
	LitStruct{struct_name: String, values: Vec<(String, Expr)>},
	Proj(Box<Expr>, String),
	Call(Box<Expr>, Vec<Expr>),
	Cast(Ty, Box<Expr>),
	Binop(Box<Expr>, BinaryOp, Box<Expr>),
	Unop(UnaryOp, Box<Expr>),
	GetRef(Box<Expr>),
	Deref(Box<Expr>)
}

#[derive(Debug)]
pub enum Stmt{
	Assign(Expr, Expr),
	Decl(Ty, String),
	Return(Option<Expr>),
	BareExpr(Expr),
	If(Expr, Block, Block),
	While(Expr, Block)
}

type Block = Vec<Stmt>;

#[derive(Debug)]
pub enum PolymorphMode{
	Separated,
	Erased
}

#[derive(Debug)]
pub enum Gdecl{
	GVarDecl(Ty, String),
	GFuncDecl{ret_type: Option<Ty>, name: String, args: Vec<(Ty, String)>, body: Block},
	GStructDecl{name: String, fields: Vec<(Ty, String)>},
	GGenericStructDecl{name: String, param: String, mode: PolymorphMode, fields: Vec<(Ty, String)>},
	GGenericFuncDecl{name: String, ret_type: Option<Ty>, args: Vec<(Ty, String)>, body: Block, param: String, mode: PolymorphMode}
}
