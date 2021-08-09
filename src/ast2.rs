use crate::ast;
#[derive(Debug, Clone)]
pub struct Loc<T> {
	pub elt: T,
	pub byte_offset: usize,
	pub byte_len: usize,
	pub file_id: u16
}
impl<'arena, T> Loc<T> {
	pub fn alloc(self, arena: &'arena bumpalo::Bump) -> Loc<&'arena mut T> {
		Loc{
			elt: arena.alloc(self.elt),
			byte_offset: self.byte_offset,
			byte_len: self.byte_len,
			file_id: self.file_id
		}
	}
}

impl<T: Copy> Copy for Loc<T> {}

//Some traits (like Debug and Clone) can just be derived, but some traits need to have customized behavior
//to ignore the location info and just defer to .elt
impl<T> std::ops::Deref for Loc<T> {
	type Target = T;
	fn deref(&self) -> &Self::Target {
		&self.elt
	}
}

use std::hash::Hash;
impl<T: Hash> Hash for Loc<T> {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		self.elt.hash(state)
	}
}

impl<T: PartialEq> PartialEq for Loc<T> {
	fn eq(&self, other: &Self) -> bool {
		self.elt == other.elt
	}
}
impl<T: Eq> Eq for Loc<T> {}

use std::fmt::Display;
impl<T: Display> Display for Loc<T> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", &self.elt)
	}
}

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
	pub fn to_owned_ast(self) -> ast::IntSize {
		match self {
			IntSize::Size8 => ast::IntSize::Size8,
			IntSize::Size16 => ast::IntSize::Size16,
			IntSize::Size32 => ast::IntSize::Size32,
			IntSize::Size64 => ast::IntSize::Size64,
		}
	}
}
impl Display for IntSize {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.num_bits())
	}
}

///The different sizes a floating-point type can have.
#[derive(Debug, PartialEq, Clone, PartialOrd, Copy, Eq, Hash)]
pub enum FloatSize{
	FSize32,
	FSize64
}
impl FloatSize{
	pub fn to_owned_ast(self) -> ast::FloatSize {
		match self {
			FloatSize::FSize32 => ast::FloatSize::FSize32,
			FloatSize::FSize64 => ast::FloatSize::FSize64
		}
	}
}
impl Display for FloatSize {
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

///'arena here means it refers to the typecache, not the bumpalo arena (they have the same lifetime though)
///types cannot have each component wrapped in a Loc<> because the location info would be cached, and would be wrong when
///using a cached type.
///If I really want to, I could add Loc<> to each node, and store whatever location in the cache,
///and only use the more accurate error reporting when the type has a "depth" of < 2 (this is the common case,
///i32* is a lot more common than i32**). Whenever a Ty generates an error, check if the Ty's depth is >= 2, and use
///the base location if it is.
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum Ty<'src, 'arena> where 'src: 'arena { //'src lives longer than 'arena
	Bool,
	Int{signed: bool, size: IntSize},
	Float(FloatSize),
	Ptr(Option<&'arena Ty<'src, 'arena>>),
	Array{length: u64, typ: &'arena Ty<'src, 'arena>},
	Struct(&'src str),
	TypeVar(&'src str),
	GenericStruct{type_param: &'arena Ty<'src, 'arena>, name: &'src str}
}
///Responsible for distributing &'arena Ty<'src, 'arena>
///To construct a new type, check if it is in the hashmap
///If it is, just use that, otherwise, allocate it in the arena,
///then update the hashmap to hold the reference you just got
use std::sync::{RwLock, Mutex};
use std::collections::HashMap;
pub struct TypeCache<'src, 'arena> where 'src: 'arena {
	pub arena: Mutex<&'arena mut bumpalo::Bump>,
	pub cached: RwLock< HashMap<Ty<'src, 'arena>, &'arena Ty<'src, 'arena>> >
}
impl<'src, 'arena> Ty<'src, 'arena> where 'src: 'arena {
	///Recurses through a type, returning the type variable that it contains, if any.
	///
	///```
	///use Ty::*;
	///let t1 = Ptr(Some(&TypeVar("T"))); //'T*
	///assert_eq!(t1.recursively_find_type_var(), Some("T"));
	///let t2 = Ptr(Some(&Bool)); //bool*
	///assert_eq!(t1.recursively_find_type_var(), None);
	///let t3 = GenericStruct{
	///    type_param: &Array{
	///        length: 10,
	///        typ: &TypeVar("S")
	///    },
	///    name: "vec"
	///}; //struct vec@<'T[10]>
	///assert_eq!(t3.recursively_find_type_var(), Some("S"));
	///```
	pub fn recursively_find_type_var(&self) -> Option<&'src str> {
		use Ty::*;
		match self {
			Bool | Int{..} | Float(_) | Struct(_) | Ptr(None) => None,
			Ptr(Some(nested)) | Array{typ: nested, ..} | GenericStruct{type_param: nested, ..} =>
				nested.recursively_find_type_var(),
			TypeVar(s) => Some(s),
		}
	}

	//when a new type is created, call this method on it to see if it is in the cache
	//if it is, this method will return a reference to the place in the arena where it already exists
	//if it is not, this method will allocate it in the arena, and return a reference to it
	pub fn getref(&self, cache: &'arena TypeCache<'src, 'arena>) -> &'arena Self {
		let read_access = cache.cached.read().unwrap();
		let cached_result: Option<&'arena Ty<'src, 'arena>> = read_access.get(self).cloned();
		drop(read_access);
		if let Some(cached) = cached_result {
			cached
		} else {
			/*
			It's possible for 2 threads to see that a type is not in self.cached, and both of them try to allocate it.
			If this happens, and 2 threads are in this else block at the same time, they should both try to get write access first.
			One will get the access and allocate the type, the other will see that it the type has already been allocated, and return it.
			It should be faster to do this rather than always getting write access because seeing a type that is already cached
			is much more common, and multiple threads should be able to do that at the same time.
			*/
			let mut write_access = cache.cached.write().unwrap();
			if let Some(cached) = cached_result {
				return cached;
			}
			/*
			I can't clone a & &'arena Bump that came from a & &'arena mut Bump because another thread could obtain
			the &'arena mut bump while I still have the &'arena Bump
			*/
			let lock_guard = cache.arena.lock().unwrap();
			let arenaref: & &'arena mut bumpalo::Bump = &lock_guard;
			let arenaref: &'arena bumpalo::Bump = unsafe {
				*(arenaref as *const &'arena mut bumpalo::Bump) as &'arena bumpalo::Bump
			};
			let new_alloc: &'arena Ty<'src, 'arena> = arenaref.alloc(self.clone());
			drop(lock_guard);
			write_access.insert(self.clone(), new_alloc);
			new_alloc
			//todo!()
		}
	}

	//actually does the work of replace_type_var_with, but does not check if the type contains a
	//type var, which should be done to avoid doing unnecessary work.
	fn do_replacement(&'arena self, replacement: &'arena Ty<'src, 'arena>, cache: &'arena TypeCache<'src, 'arena>) -> &'arena Ty<'src, 'arena> {
		use Ty::*;
		match self {
			TypeVar(s) => {
				debug_assert!(*s != "_should_not_happen", "TypeVar is _should_not_happen");
				replacement
			},
			Ptr(Some(t)) => {
				let replaced = Ptr(Some(t.do_replacement(replacement, cache)));
				replaced.getref(cache)
			}
			Array{typ, length} => {
				let replaced = Array{typ: typ.do_replacement(replacement, cache), length: *length};
				replaced.getref(cache)
			},
			GenericStruct{type_param, name} => {
				let replaced = GenericStruct{type_param: type_param.do_replacement(replacement, cache), name};
				replaced.getref(cache)
			},
			other => other
		}
	}

	//TODO: make a new method here that does the checks if the type var found is the same as the one given, like the similar function in typechecker.rs

	pub fn replace_type_var_with(&'arena self, replacement: &'arena Self, cache: &'arena TypeCache<'src, 'arena>) -> &'arena Self {
		if self.recursively_find_type_var().is_some() {
			self.do_replacement(replacement, cache)
		} else {
			self
		}
	}

	/*
	///Determines if a type recursively contains an erased struct, and therefore is dynamically sized
	#[allow(non_snake_case)]
	pub fn is_DST(&self, structs: &super::typechecker::StructContext, mode: Option<PolymorphMode>) -> bool {
		use Ty::*;
		use super::typechecker::StructType::*;
		match self {
			GenericStruct{name, type_param} => match structs.get(name).unwrap() {
				Generic{mode: PolymorphMode::Erased, fields: _, type_var: _} => true,
				Generic{mode: PolymorphMode::Separated, fields, type_var: _} => {
					/* parallel version, might not be worth it because most structs will not have that many fields
					fields.par_iter()
						.any(|(_, t)| t.clone().replace_type_var_with(type_param).is_DST(structs, mode))
					*/
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
	*/

	///Helper function to call `replace_type_var_with` when the replacement is an Option that should only be unwrapped if self
	///contains a TypeVar
	pub fn concretized(&'arena self, replacement: Option<&'arena Self>, arena: &'arena TypeCache<'src, 'arena>) -> &'arena Self {
		if self.recursively_find_type_var().is_some() {
			let replacement = replacement.unwrap_or_else(|| panic!("Tried to concretize {:?}, which contains type var '{}, but replacement was None", &self, self.recursively_find_type_var().unwrap()));
			self.do_replacement(replacement, arena)
		} else {
			self
		}
	}

	pub fn to_owned_ast(&self) -> ast::Ty {
		use Ty::*;
		match self {
			Bool => ast::Ty::Bool,
			Int{signed, size} => ast::Ty::Int{signed: *signed, size: size.to_owned_ast()},
			Float(size) => ast::Ty::Float(size.to_owned_ast()),
			Ptr(None) => ast::Ty::Ptr(None),
			Ptr(Some(t)) => ast::Ty::Ptr(Some(Box::new(t.to_owned_ast()))),
			Array{length, typ} => ast::Ty::Array{length: *length, typ: Box::new(typ.to_owned_ast())},
			Struct(s) => ast::Ty::Struct((*s).to_owned()),
			TypeVar(s) => ast::Ty::TypeVar((*s).to_owned()),
			GenericStruct{type_param, name} => ast::Ty::GenericStruct{type_param: Box::new(type_param.to_owned_ast()), name: (*name).to_owned()}
		}
	}

}

impl<'src, 'arena> Display for Ty<'src, 'arena> {
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
			GenericStruct{type_param, name} => write!(f, "struct {} @<{}>", name, type_param)
		}
	}
}


#[derive(Debug, PartialEq, Clone, Copy)]
pub enum UnaryOp{
	Neg, Lognot, Bitnot
}
impl UnaryOp {
	pub fn to_owned_ast(self) -> ast::UnaryOp {
		use UnaryOp::*;
		match self {
			Neg => ast::UnaryOp::Neg,
			Lognot => ast::UnaryOp::Lognot,
			Bitnot => ast::UnaryOp::Bitnot
		}
	}
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
impl BinaryOp {
	pub fn to_owned_ast(self) -> ast::BinaryOp {
		use BinaryOp::*;
		match self {
			Add => ast::BinaryOp::Add,
			Sub => ast::BinaryOp::Sub,
			Mul => ast::BinaryOp::Mul,
			Div => ast::BinaryOp::Div,
			Mod => ast::BinaryOp::Mod,
			Equ => ast::BinaryOp::Equ,
			Neq => ast::BinaryOp::Neq,
			Lt => ast::BinaryOp::Lt,
			Lte => ast::BinaryOp::Lte,
			Gt => ast::BinaryOp::Gt,
			Gte => ast::BinaryOp::Gte,
			And => ast::BinaryOp::And,
			Or => ast::BinaryOp::Or,
			Bitand => ast::BinaryOp::Bitand,
			Bitor => ast::BinaryOp::Bitor,
			Bitxor => ast::BinaryOp::Bitxor,
			Shl => ast::BinaryOp::Shl,
			Shr => ast::BinaryOp::Shr,
			Sar => ast::BinaryOp::Sar
		}
	}
}

use std::borrow::Cow;
#[derive(Debug, PartialEq)]
pub enum Expr<'src, 'arena> where 'src: 'arena {
	LitNull,
	LitBool(bool),
	LitSignedInt(i64, IntSize),
	LitUnsignedInt(u64, IntSize),
	LitFloat(f64, FloatSize),
	LitString(Cow<'src, str>),
	Id(&'src str),
	Index(Loc<&'arena mut TypedExpr<'src, 'arena>>, Loc<&'arena mut TypedExpr<'src, 'arena>>),
	Proj(Loc<&'arena mut TypedExpr<'src, 'arena>>, Loc<&'src str>),
	//when dealing with a slice of ast items, should I wrap the slice in a Loc? I think it's ok to just use the loc of
	//the containing item (e.g. wrong number of args to function)
	Call(Loc<&'src str>, &'arena mut [Loc<TypedExpr<'src, 'arena>>]),
	GenericCall{name: Loc<&'src str>, type_param: Loc<&'arena Ty<'src, 'arena>>, args: &'arena mut [Loc<TypedExpr<'src, 'arena>>]},
	Cast(Loc<&'arena Ty<'src, 'arena>>, Loc<&'arena mut TypedExpr<'src, 'arena>>),
	Binop(Loc<&'arena mut TypedExpr<'src, 'arena>>, BinaryOp, Loc<&'arena mut TypedExpr<'src, 'arena>>),
	Unop(UnaryOp, Loc<&'arena mut TypedExpr<'src, 'arena>>),
	GetRef(Loc<&'arena mut TypedExpr<'src, 'arena>>),
	Deref(Loc<&'arena mut TypedExpr<'src, 'arena>>),
	Sizeof(Loc<&'arena Ty<'src, 'arena>>)
}
impl<'src: 'arena, 'arena> Expr<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::Expr {
		use Expr::*;
		match self {
			LitNull => ast::Expr::LitNull,
			LitBool(b) => ast::Expr::LitBool(*b),
			LitSignedInt(val, size) => ast::Expr::Cast(ast::Ty::Int{signed: true, size: size.to_owned_ast()}, Box::new(ast::Expr::LitSignedInt(*val))),
			LitUnsignedInt(val, size) => ast::Expr::Cast(ast::Ty::Int{signed: false, size: size.to_owned_ast()}, Box::new(ast::Expr::LitUnsignedInt(*val))),
			LitFloat(f, FloatSize::FSize64) => ast::Expr::LitFloat(*f),
			LitFloat(f, FloatSize::FSize32) => ast::Expr::Cast(ast::Ty::Float(ast::FloatSize::FSize32), Box::new(ast::Expr::LitFloat(*f))),
			LitString(s) => ast::Expr::LitString(s.clone().into_owned()),
			Id(s) => ast::Expr::Id((*s).to_owned()),
			Index(base_loc, index_loc) => ast::Expr::Index(Box::new(base_loc.elt.expr.to_owned_ast()), Box::new(index_loc.elt.expr.to_owned_ast())),
			Proj(base_loc, field) => ast::Expr::Proj(Box::new(base_loc.elt.expr.to_owned_ast()), field.elt.to_owned()),
			Call(name_loc, arg_locs) => ast::Expr::Call(name_loc.elt.to_owned(), arg_locs.iter().map(|e| e.elt.expr.to_owned_ast()).collect()),
			GenericCall{name, type_param, args} =>
				ast::Expr::GenericCall{name: name.elt.to_owned(), type_param: type_param.elt.to_owned_ast(), args: args.iter().map(|e| e.elt.expr.to_owned_ast()).collect()},
			Cast(ty_loc, e_loc) => ast::Expr::Cast(ty_loc.elt.to_owned_ast(), Box::new(e_loc.elt.expr.to_owned_ast())),
			Binop(lhs_loc, op, rhs_loc) => ast::Expr::Binop(
				Box::new(lhs_loc.elt.expr.to_owned_ast()),
				op.to_owned_ast(),
				Box::new(rhs_loc.elt.expr.to_owned_ast()),
			),
			Unop(op, e_loc) => ast::Expr::Unop(op.to_owned_ast(), Box::new(e_loc.elt.expr.to_owned_ast())),
			GetRef(e_loc) => ast::Expr::GetRef(Box::new(e_loc.elt.expr.to_owned_ast())),
			Deref(e_loc) => ast::Expr::Deref(Box::new(e_loc.elt.expr.to_owned_ast())),
			Sizeof(ty_loc) => ast::Expr::Sizeof(ty_loc.elt.to_owned_ast())
		}
	}
}

#[derive(Debug, PartialEq)]
pub struct TypedExpr<'src, 'arena> where 'src: 'arena {
	pub expr: Expr<'src, 'arena>,
	pub typ: Option<&'arena Ty<'src, 'arena>>
}
impl<'src: 'arena, 'arena> From<Expr<'src, 'arena>> for TypedExpr<'src, 'arena> {
	fn from(e: Expr<'src, 'arena>) -> TypedExpr<'src, 'arena> {
		TypedExpr{
			expr: e,
			typ: None
		}
	}
}

#[derive(Debug, PartialEq)]
pub enum Stmt<'src, 'arena> where 'src: 'arena {
	Assign(Loc<TypedExpr<'src, 'arena>>, Loc<TypedExpr<'src, 'arena>>),
	Decl(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>),
	Return(Option<Loc<TypedExpr<'src, 'arena>>>),
	SCall(Loc<&'src str>, &'arena mut [Loc<TypedExpr<'src, 'arena>>]),
	GenericSCall{name: Loc<&'src str>, type_param: Loc<&'arena Ty<'src, 'arena>>, args: &'arena mut [Loc<TypedExpr<'src, 'arena>>]},
	If(Loc<TypedExpr<'src, 'arena>>, Block<'src, 'arena>, Block<'src, 'arena>),
	While(Loc<TypedExpr<'src, 'arena>>, Block<'src, 'arena>)
}
impl<'src: 'arena, 'arena> Stmt<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::Stmt {
		use Stmt::*;
		match self {
			Assign(lhs_loc, rhs_loc) => ast::Stmt::Assign(lhs_loc.elt.expr.to_owned_ast(), rhs_loc.elt.expr.to_owned_ast()),
			Decl(ty_loc, name_loc) => ast::Stmt::Decl(ty_loc.elt.to_owned_ast(), name_loc.elt.to_owned()),
			Return(None) => ast::Stmt::Return(None),
			Return(Some(e_loc)) => ast::Stmt::Return(Some(e_loc.elt.expr.to_owned_ast())),
			SCall(name_loc, arg_locs) => ast::Stmt::SCall(name_loc.elt.to_owned(), arg_locs.iter().map(|e| e.elt.expr.to_owned_ast()).collect()),
			GenericSCall{name, type_param, args} =>
				ast::Stmt::GenericSCall{name: name.elt.to_owned(), type_param: type_param.elt.to_owned_ast(), args: args.iter().map(|e| e.elt.expr.to_owned_ast()).collect()},
			If(cond_loc, then_block, else_block) => ast::Stmt::If(cond_loc.elt.expr.to_owned_ast(), then_block.to_owned_ast(), else_block.to_owned_ast()),
			While(cond_loc, block) => ast::Stmt::While(cond_loc.elt.expr.to_owned_ast(), block.to_owned_ast())
		}
	}
}

#[derive(Debug, PartialEq)]
pub struct Block<'src, 'arena>(pub &'arena mut [Loc<Stmt<'src, 'arena>>]);
impl<'src: 'arena, 'arena> Block<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::Block {
		self.0.iter().map(|s| s.elt.to_owned_ast()).collect()
	}
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum PolymorphMode{
	Separated,
	Erased
}
impl PolymorphMode {
	pub fn to_owned_ast(self) -> ast::PolymorphMode {
		use PolymorphMode::*;
		match self {
			Separated => ast::PolymorphMode::Separated,
			Erased => ast::PolymorphMode::Erased
		}
	}
}

#[derive(Debug, PartialEq)]
pub enum Gdecl<'src, 'arena> where 'src: 'arena {
	Extern{
		ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
		name: Loc<&'src str>,
		arg_types: &'arena [Loc<&'arena Ty<'src, 'arena>>]
	},
	GVarDecl(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>),
	GFuncDecl{
		ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
		name: Loc<&'src str>,
		args: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)],
		body: Block<'src, 'arena>
	},
	GStructDecl{
		name: Loc<&'src str>,
		fields: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)]
	},
	GGenericStructDecl{
		name: Loc<&'src str>,
		var: Loc<&'src str>,
		mode: Loc<PolymorphMode>,
		fields: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)]
	},
	GGenericFuncDecl{
		name: Loc<&'src str>,
		ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
		args: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)],
		body: Block<'src, 'arena>,
		var: Loc<&'src str>,
		mode: Loc<PolymorphMode>
	}
}
//typecheck_program expects a &[ast::Gdecl], so I need a .to_owned_ast() for this enum
impl <'src: 'arena, 'arena> Gdecl<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::Gdecl {
		use Gdecl::*;
		match self {
			Extern{ret_type, name, arg_types} => ast::Gdecl::Extern{
				ret_type: ret_type.elt.map(|t| t.to_owned_ast()),
				name: name.elt.to_owned(),
				arg_types: arg_types.iter().map(|t| t.elt.to_owned_ast()).collect()
			},
			GVarDecl(t_loc, name_loc) => ast::Gdecl::GVarDecl(t_loc.elt.to_owned_ast(), name_loc.elt.to_owned()),
			GFuncDecl{ret_type, name, args, body} => ast::Gdecl::GFuncDecl{
				ret_type: ret_type.elt.map(|t| t.to_owned_ast()),
				name: name.elt.to_owned(),
				args: args.iter().map(|(t, name)| (t.elt.to_owned_ast(), name.elt.to_owned())).collect(),
				body: body.to_owned_ast()
			},
			GStructDecl{name, fields} => ast::Gdecl::GStructDecl{
				name: name.elt.to_owned(),
				fields: fields.iter().map(|(t, name)| (t.elt.to_owned_ast(), name.elt.to_owned())).collect(),
			},
			GGenericFuncDecl{ret_type, name, args, body, mode, var} => ast::Gdecl::GGenericFuncDecl{
				ret_type: ret_type.elt.map(|t| t.to_owned_ast()),
				name: name.elt.to_owned(),
				args: args.iter().map(|(t, name)| (t.elt.to_owned_ast(), name.elt.to_owned())).collect(),
				body: body.to_owned_ast(),
				mode: mode.to_owned_ast(),
				var: var.elt.to_owned(),
			},
			GGenericStructDecl{name, fields, mode, var} => ast::Gdecl::GGenericStructDecl{
				name: name.elt.to_owned(),
				fields: fields.iter().map(|(t, name)| (t.elt.to_owned_ast(), name.elt.to_owned())).collect(),
				mode: mode.to_owned_ast(),
				var: var.elt.to_owned(),
			}
		}
	}
}

pub struct Func<'src: 'arena, 'arena> {
	pub ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
	pub name: Loc<&'src str>,
	pub args: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)],
	pub body: Block<'src, 'arena>,
}
impl<'src: 'arena, 'arena> Func<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::Func {
		ast::Func{
			ret_type: self.ret_type.elt.map(|t| t.to_owned_ast()),
			name: self.name.elt.to_owned(),
			args: self.args.iter().map(|(t, name)| (t.elt.to_owned_ast(), name.elt.to_owned())).collect(),
			body: self.body.to_owned_ast()
		}
	}
}

pub struct Struct<'src: 'arena, 'arena> {
	pub name: Loc<&'src str>,
	pub fields: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)]
}
impl<'src: 'arena, 'arena> Struct<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::Struct {
		ast::Struct{
			name: self.name.elt.to_owned(),
			fields: self.fields.iter().map(|(t, name)| (t.elt.to_owned_ast(), name.elt.to_owned())).collect(),
		}
	}
}

pub struct GenericStruct<'src: 'arena, 'arena> {
	pub name: Loc<&'src str>,
	pub var: Loc<&'src str>,
	pub fields: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)]
}
impl<'src: 'arena, 'arena> GenericStruct<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::GenericStruct {
		ast::GenericStruct{
			name: self.name.elt.to_owned(),
			var: self.var.elt.to_owned(),
			fields: self.fields.iter().map(|(t, name)| (t.elt.to_owned_ast(), name.elt.to_owned())).collect(),
		}
	}
}

pub struct GenericFunc<'src: 'arena, 'arena> {
	pub ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
	pub name: Loc<&'src str>,
	pub args: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)],
	pub body: Block<'src, 'arena>,
	pub var: Loc<&'src str>,
}
impl<'src: 'arena, 'arena> GenericFunc<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::GenericFunc {
		ast::GenericFunc{
			ret_type: self.ret_type.elt.map(|t| t.to_owned_ast()),
			name: self.name.elt.to_owned(),
			args: self.args.iter().map(|(t, name)| (t.elt.to_owned_ast(), name.elt.to_owned())).collect(),
			body: self.body.to_owned_ast(),
			var: self.var.elt.to_owned()
		}
	}
}

pub struct ExternalFunc<'src: 'arena, 'arena> {
	pub name: Loc<&'src str>,
	pub ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
	pub arg_types: &'arena [Loc<&'arena Ty<'src, 'arena>>]
}
impl<'src: 'arena, 'arena> ExternalFunc<'src, 'arena> {
	pub fn to_owned_ast(&self) -> ast::ExternalFunc {
		ast::ExternalFunc{
			ret_type: self.ret_type.elt.map(|t| t.to_owned_ast()),
			name: self.name.elt.to_owned(),
			arg_types: self.arg_types.iter().map(|t| t.elt.to_owned_ast()).collect(),
		}
	}
}

//I don't need to know the location of an entire function, so not wrapping Func, Struct, etc. in Loc<> here
pub struct Program<'src: 'arena, 'arena> {
	pub external_funcs: &'arena [ExternalFunc<'src, 'arena>],
	pub global_vars: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)],
	pub funcs: &'arena [Func<'src, 'arena>],
	pub structs: &'arena [Struct<'src, 'arena>],
	pub erased_structs: &'arena [GenericStruct<'src, 'arena>],
	pub separated_structs: &'arena [GenericStruct<'src, 'arena>],
	pub erased_funcs: &'arena [GenericFunc<'src, 'arena>],
	pub separated_funcs: &'arena [GenericFunc<'src, 'arena>],
}

impl<'src, 'arena> Program<'src, 'arena> {
	pub fn from_gdecls(mut gdecls: Vec<Gdecl<'src, 'arena>>, arena: &'arena bumpalo::Bump) -> Self {
		//count how many of each type of gdecl there are
		let mut num_externs = 0;
		let mut num_globals = 0;
		let mut num_funcs = 0;
		let mut num_structs = 0;
		let mut num_erased_structs = 0;
		let mut num_separated_structs = 0;	
		let mut num_erased_funcs = 0;
		let mut num_separated_funcs = 0;
		use Gdecl::*;
		for gdecl in gdecls.iter() { match gdecl {
			Extern{..} => num_externs += 1,
			GVarDecl(_,_) => num_globals += 1,
			GFuncDecl{..} => num_funcs += 1,
			GStructDecl{..} => num_structs += 1,
			GGenericStructDecl{mode: Loc{elt: PolymorphMode::Erased, ..}, ..} => num_erased_structs += 1,
			GGenericStructDecl{mode: Loc{elt: PolymorphMode::Separated, ..}, ..} => num_separated_structs += 1,
			GGenericFuncDecl{mode: Loc{elt: PolymorphMode::Erased, ..}, ..} => num_erased_funcs += 1,
			GGenericFuncDecl{mode: Loc{elt: PolymorphMode::Separated, ..}, ..} => num_separated_funcs += 1,
		}}
		//I need to take the Gdecl out of gdecls, but in an arbitrary order, so into_iter won't work.
		//mem::replace each one with a dummy gdecl
		let get_dummy = || {
			Gdecl::Extern{
				ret_type: Loc{elt: None, byte_offset: 0, byte_len: 0, file_id: 0},
				name: Loc{elt: "", byte_offset: 0, byte_len: 0, file_id: 0},
				arg_types: &[]
			}
		};
		//because the dummy is an Extern, must process the externs first
		use std::mem::replace;
		let mut just_externs = gdecls.iter_mut().filter_map(|g: &mut Gdecl<'src, 'arena>| {
			if matches!(g, Extern{..}) {
				match replace(g, get_dummy()) {
					Extern{name, ret_type, arg_types} => Some(ExternalFunc{name, ret_type, arg_types}),
					_ => unreachable!()
				}
			} else { None }
		});
		//just_externs isn't an ExactSizeIterator, so I can't use arena.alloc_slice_fill_iter()
		let external_funcs: &'arena [ExternalFunc<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_externs, |_| just_externs.next().unwrap());
		debug_assert!(just_externs.next().is_none(), "More externs than expected, num_externs = {}", num_externs);

		let mut just_globals = gdecls.iter_mut().filter_map(|g| {
			if matches!(g, GVarDecl(_,_)) {
				match replace(g, get_dummy()) {
					GVarDecl(ty, name) => Some((ty, name)),
					_ => unreachable!()
				}
			} else { None }
		});
		let global_vars: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)] =
			arena.alloc_slice_fill_with(num_globals, |_| just_globals.next().unwrap());
		debug_assert!(just_globals.next().is_none(), "More globals than expected, num_globals = {}", num_globals);

		let mut just_funcs = gdecls.iter_mut().filter_map(|g| {
			if matches!(g, GFuncDecl{..}) {
				match replace(g, get_dummy()) {
					GFuncDecl{ret_type, name, args, body} => Some(Func{ret_type, name, args, body}),
					_ => unreachable!()
				}
			} else { None }
		});
		let funcs: &'arena [Func<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_funcs, |_| just_funcs.next().unwrap());
		debug_assert!(just_funcs.next().is_none(), "More funcs than expected, num_funcs = {}", num_funcs);

		let mut just_structs = gdecls.iter_mut().filter_map(|g| {
			if matches!(g, GStructDecl{..}) {
				match replace(g, get_dummy()) {
					GStructDecl{name, fields} => Some(Struct{name, fields}),
					_ => unreachable!()
				}
			} else { None }
		});
		let structs: &'arena [Struct<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_structs, |_| just_structs.next().unwrap());
		debug_assert!(just_structs.next().is_none(), "More structs than expected, num_structs = {}", num_structs);

		let mut just_erased_structs = gdecls.iter_mut().filter_map(|g| {
			if matches!(g, GGenericStructDecl{mode: Loc{elt: PolymorphMode::Erased, ..}, ..}) {
				match replace(g, get_dummy()) {
					GGenericStructDecl{name, var, fields, ..} => Some(GenericStruct{name, var, fields}),
					_ => unreachable!()
				}
			} else { None }
		});
		let erased_structs: &'arena [GenericStruct<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_erased_structs, |_| just_erased_structs.next().unwrap());
		debug_assert!(just_erased_structs.next().is_none(), "More erased structs than expected, num_erased_structs = {}", num_erased_structs);

		let mut just_separated_structs = gdecls.iter_mut().filter_map(|g| {
			if matches!(g, GGenericStructDecl{mode: Loc{elt: PolymorphMode::Separated, ..}, ..}) {
				match replace(g, get_dummy()) {
					GGenericStructDecl{name, var, fields, ..} => Some(GenericStruct{name, var, fields}),
					_ => unreachable!()
				}
			} else { None }
		});
		let separated_structs: &'arena [GenericStruct<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_separated_structs, |_| just_separated_structs.next().unwrap());
		debug_assert!(just_separated_structs.next().is_none(), "More separated structs than expected, num_separated_structs = {}", num_separated_structs);

		let mut just_erased_funcs = gdecls.iter_mut().filter_map(|g| {
			if matches!(g, GGenericFuncDecl{mode: Loc{elt: PolymorphMode::Separated, ..}, ..}) {
				match replace(g, get_dummy()) {
					GGenericFuncDecl{ret_type, name, args, body, var, ..} => Some(GenericFunc{ret_type, name, args, body, var}),
					_ => unreachable!()
				}
			} else { None }
		});
		let erased_funcs: &'arena [GenericFunc<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_erased_funcs, |_| just_erased_funcs.next().unwrap());
		debug_assert!(just_erased_funcs.next().is_none(), "More erased funcs than expected, num_erased_funcs = {}", num_erased_funcs);

		let mut just_separated_funcs = gdecls.iter_mut().filter_map(|g| {
			if matches!(g, GGenericFuncDecl{mode: Loc{elt: PolymorphMode::Separated, ..}, ..}) {
				match replace(g, get_dummy()) {
					GGenericFuncDecl{ret_type, name, args, body, var, ..} => Some(GenericFunc{ret_type, name, args, body, var}),
					_ => unreachable!()
				}
			} else { None }
		});
		let separated_funcs: &'arena [GenericFunc<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_separated_funcs, |_| just_separated_funcs.next().unwrap());
		debug_assert!(just_separated_funcs.next().is_none(), "More separated funcs than expected, num_separated_funcs = {}", num_separated_funcs);

		Program {
			external_funcs,
			global_vars,
			funcs,
			structs,
			erased_structs,
			separated_structs,
			erased_funcs,
			separated_funcs
		}
	}
	
	pub fn to_owned_ast(&self) -> ast::Program {
		ast::Program{
			external_funcs: self.external_funcs.iter().map(|e| e.to_owned_ast()).collect(),
			global_vars: self.global_vars.iter().map(|(ty_loc, name_loc)| (ty_loc.elt.to_owned_ast(), name_loc.elt.to_owned())).collect(),
			funcs: self.funcs.iter().map(|e| e.to_owned_ast()).collect(),
			structs: self.structs.iter().map(|e| e.to_owned_ast()).collect(),
			erased_structs: self.erased_structs.iter().map(|e| e.to_owned_ast()).collect(),
			separated_structs: self.separated_structs.iter().map(|e| e.to_owned_ast()).collect(),
			erased_funcs: self.erased_funcs.iter().map(|e| e.to_owned_ast()).collect(),
			separated_funcs: self.separated_funcs.iter().map(|e| e.to_owned_ast()).collect(),
		}
	}
}
