enum IntSize{
	Size8,
	Size16,
	Size32,
	Size64
}
enum Ty{
	Bool,
	Int{signed: bool, size: IntSize},
	Ptr(Box<Ty>),
	Struct(String)
}

enum UnaryOp{
	Neg,
	Lognot,
	Bitnot
}

enum BinaryOp{
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

enum Expr{
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
	Unop(UnaryOp, Box<Expr>)
}

enum Stmt{
	Assign(Expr, Expr),
	Decl(Ty, String),
	Return(Option<Expr>),
	BareExpr(Expr),
	If(Expr, Block, Block),
	While(Expr, Block)
}

type Block = Vec<Stmt>;

enum Gdecl{
	GVarDecl(Ty, String),
	GFuncDecl{ret_type: Option<Ty>, name: String, args: Vec<(Ty, String)>, body: Block},
	GStructDecl(String, Vec<(Ty, String)>)
}
