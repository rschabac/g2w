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
	Ptr(Option<Box<Ty>>),	//void pointers are represented as Ptr(None)
	Array{length: u32, typ: Box<Ty>},
	Struct(String),
	TypeVar(String),
}

#[derive(Debug, PartialEq)]
pub enum UnaryOp{
	Neg,
	Lognot,
	Bitnot
}

#[derive(Debug, PartialEq)]
pub enum BinaryOp{
	Add,
	Sub,
	Mul,
	Div,
	Mod,
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
	Shl,	//<<
	Shr,	//>>
	Sar		//>>>
}

#[derive(Debug, PartialEq)]
pub enum Expr{
	LitNull,
	LitBool(bool),
	//For the time being, all integer literals will be 64 bits
	LitSignedInt(i64),
	LitUnsignedInt(u64),
	LitString(String),
	Id(String),
	//Type of an array literal will be inferred based on the first element
	LitArr(Vec<Expr>),
	Index(Box<Expr>, Box<Expr>),
	//maybe add this back in later
	//LitStruct{struct_name: String, values: Vec<(String, Expr)>},
	Proj(Box<Expr>, String),
	Call(Box<Expr>, Vec<Expr>),
	Cast(Ty, Box<Expr>),
	Binop(Box<Expr>, BinaryOp, Box<Expr>),
	Unop(UnaryOp, Box<Expr>),
	GetRef(Box<Expr>),
	Deref(Box<Expr>),
	Sizeof(Ty)
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
