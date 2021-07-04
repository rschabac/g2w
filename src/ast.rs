#[derive(Debug, PartialEq, Clone, PartialOrd, Copy, Eq, Hash)]
pub enum IntSize{
	Size8,
	Size16,
	Size32,
	Size64
}
impl IntSize{
	pub fn num_bits(&self) -> u8 {
		match self {
			IntSize::Size8 => 8,
			IntSize::Size16 => 16,
			IntSize::Size32 => 32,
			IntSize::Size64 => 64
		}
	}
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
impl Ty {
	pub fn recursively_find_type_var(&self) -> Option<&str> {
		use Ty::*;
		match self {
			Bool | Int{..} | Float(_) | Struct(_) | Ptr(None) => None,
			Ptr(Some(boxed)) | Array{typ: boxed, ..} | GenericStruct{type_var: boxed, ..} 
				=> boxed.recursively_find_type_var(),
			TypeVar(s) => Some(s.as_str()),
		}
	}
	
	//actually does the work, by mutating the type in place, which seems to be less convenient than returning a new Ty
	fn replace_type_var_in_place(&mut self, replacement: &Self) {
		use Ty::*;
		match self {
			TypeVar(s) => {
				debug_assert!(s != "_should_not_happen", "TypeVar is _should_not_happen");
				*self = replacement.clone()
			},
			Ptr(Some(t)) | Array{typ: t, ..} | GenericStruct{type_var: t, ..} => {t.as_mut().replace_type_var_in_place(replacement)},
			_ => ()
		}
	}
	//very similar to the function `replace_type_var_with` in typechecker.rs, but does not check
	//that the type var contained matches the type var expected
	pub fn replace_type_var_with(mut self, replacement: &Self) -> Self {
		self.replace_type_var_in_place(replacement);
		self
	}

	//returns whether or not a type contains an erased struct, and therefore is dynamically sized
	#[allow(non_snake_case)]
	pub fn is_DST(&self, structs: &super::typechecker::StructContext, mode: Option<PolymorphMode>) -> bool {
		use Ty::*;
		use super::typechecker::StructType::*;
		match self {
			GenericStruct{name, type_var: type_param} => match structs.get(name.as_str()).unwrap() {
				Generic{mode: PolymorphMode::Erased, fields: _, type_var: _} => true,
				Generic{mode: PolymorphMode::Separated, fields, type_var: _} => {
					for field_ty in fields.iter().map(|(_, t)| t.clone()) {
						if field_ty.replace_type_var_with(type_param).is_DST(structs, mode) {
							return true;
						}
					}
					false
				},
				NonGeneric(_) => panic!("struct context contains nongeneric struct for generic struct {}, should have been caught by now", name),
			},
			Struct(name) => match structs.get(name).unwrap() {
				NonGeneric(fields) => fields.iter().any(|(_, ty)| ty.is_DST(structs, mode)),
				_ => panic!("struct context contains generic struct for non-generic struct {}, should have been caught by now", name),
			},
			Array{typ, ..} => typ.as_ref().is_DST(structs, mode),
			TypeVar(_) => mode == Some(PolymorphMode::Erased),
			_ => false
		}
	}

	//helper function to call `replace_type_var_with` when the replacement is an Option that should only be unwrapped if self
	//contains a TypeVar
	pub fn concretized(self, replacement: Option<&Self>) -> Self {
		if self.recursively_find_type_var().is_some() {
			let replacement = replacement.unwrap_or_else(|| panic!("Tried to concretize {:?}, which contains type var '{}, but replacement was None", &self, self.recursively_find_type_var().unwrap()));
			self.replace_type_var_with(replacement)
		} else {
			self
		}
	}
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
	Extern{ret_type: Option<Ty>, name: String, arg_types: Vec<Ty>},
	GVarDecl(Ty, String),
	GFuncDecl{ret_type: Option<Ty>, name: String, args: Vec<(Ty, String)>, body: Block},
	GStructDecl{name: String, fields: Vec<(Ty, String)>},
	GGenericStructDecl{name: String, param: String, mode: PolymorphMode, fields: Vec<(Ty, String)>},
	GGenericFuncDecl{name: String, ret_type: Option<Ty>, args: Vec<(Ty, String)>, body: Block, param: String, mode: PolymorphMode}
}

pub struct Func{
	pub ret_type: Option<Ty>,
	pub name: String,
	pub args: Vec<(Ty, String)>,
	pub body: Block
}

pub struct Struct{
	pub name: String,
	pub fields: Vec<(Ty, String)>
}

pub struct GenericStruct{
	pub name: String,
	pub param: String,
	pub fields: Vec<(Ty, String)>
}

pub struct GenericFunc{
	pub name: String,
	pub ret_type: Option<Ty>,
	pub args: Vec<(Ty, String)>,
	pub body: Block,
	pub param: String,
}

pub struct ExternalFunc{
	pub name: String,
	pub ret_type: Option<Ty>,
	pub arg_types: Vec<Ty>
}

pub struct Program{
	pub external_funcs: Vec<ExternalFunc>,
	pub global_vars: Vec<(Ty, String)>,
	pub funcs: Vec<Func>,
	pub structs: Vec<Struct>,
	pub erased_structs: Vec<GenericStruct>,
	pub separated_structs: Vec<GenericStruct>,
	pub erased_funcs: Vec<GenericFunc>,
	pub separated_funcs: Vec<GenericFunc>
}

impl From<Vec<Gdecl>> for Program {
	fn from(gdecls: Vec<Gdecl>) -> Self {
		let mut result = Program{
			external_funcs: Vec::new(),
			global_vars: Vec::new(),
			funcs: Vec::new(),
			structs: Vec::new(),
			erased_structs: Vec::new(),
			separated_structs: Vec::new(),
			erased_funcs: Vec::new(),
			separated_funcs: Vec::new(),
		};
		use Gdecl::*;
		for gdecl in gdecls.into_iter() {
			match gdecl {
				Extern{ret_type, name, arg_types} => result.external_funcs.push(ExternalFunc{
					name, ret_type, arg_types
				}),
				GVarDecl(t, s) => result.global_vars.push((t, s)),
				GFuncDecl{ret_type, name, args, body} => result.funcs.push(Func{
					ret_type, name, args, body
				}),
				GStructDecl{name, fields} => result.structs.push(Struct{
					name, fields
				}),
				GGenericStructDecl{name, param, mode: PolymorphMode::Erased, fields} => result.erased_structs.push(GenericStruct{
					name, param, fields
				}),
				GGenericStructDecl{name, param, mode: PolymorphMode::Separated, fields} => result.separated_structs.push(GenericStruct{
					name, param, fields
				}),
				GGenericFuncDecl{name, ret_type, args, body, param, mode: PolymorphMode::Erased} => result.erased_funcs.push(GenericFunc{
					name, ret_type, args, body, param
				}),
				GGenericFuncDecl{name, ret_type, args, body, param, mode: PolymorphMode::Separated} => result.separated_funcs.push(GenericFunc{
					name, ret_type, args, body, param
				})
			}
		}
		result
	}
}
