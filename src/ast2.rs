#[derive(Debug, Clone, Copy)]
pub struct Loc<T> {
	elt: T,
	byte_offset: usize,
	byte_len: usize
}

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
		&self.elt == &other.elt
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
	arena: Mutex<&'arena bumpalo::Bump>,
	cached: RwLock< HashMap<Ty<'src, 'arena>, &'arena Ty<'src, 'arena>> >
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
	pub fn getref(self, cache: &'arena TypeCache<'src, 'arena>) -> &'arena Self {
		if let Some(cached) = cache.cached.read().unwrap().get(&self) {
			cached
		} else {
			let new_alloc: &'arena Ty<'src, 'arena> = cache.arena.lock().unwrap().alloc(self.clone());
			let mut locked = cache.cached.write().unwrap();
			locked.insert(self.clone(), new_alloc);
			new_alloc
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

}

impl<'src, 'arena> std::fmt::Display for Ty<'src, 'arena> {
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

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BinaryOp{
	Add, Sub, Mul, Div, Mod,
	Equ, Neq,
	Lt, Lte, Gt, Gte,
	And, Or,
	Bitand, Bitor, Bitxor,
	Shl /* << */, Shr /* >> */, Sar	/* >>> */
}

use std::borrow::Cow;
#[derive(Debug, PartialEq)]
pub enum Expr<'src, 'arena> where 'src: 'arena {
	LitNull,
	LitBool(bool),
	LitSignedInt(i64, IntSize),
	LitUnsignedInt(u64, IntSize),
	LitFloat(f64),
	LitString(Cow<'src, str>),
	Id(&'src str),
	Index(Loc<&'arena Expr<'src, 'arena>>, Loc<&'arena Expr<'src, 'arena>>),
	Proj(Loc<&'arena Expr<'src, 'arena>>, Loc<&'src str>),
	//when dealing with a slice of ast items, should I wrap the slice in a Loc? I think it's ok to just use the loc of
	//the containing item (e.g. wrong number of args to function)
	Call(Loc<&'src str>, &'arena [Loc<Expr<'src, 'arena>>]),
	GenericCall{name: Loc<&'src str>, type_param: Loc<&'arena Ty<'src, 'arena>>, args: &'arena [Loc<Expr<'src, 'arena>>]},
	Cast(Loc<&'arena Ty<'src, 'arena>>, Loc<&'arena Expr<'src, 'arena>>),
	Binop(Loc<&'arena Expr<'src, 'arena>>, BinaryOp, Loc<&'arena Expr<'src, 'arena>>),
	Unop(UnaryOp, Loc<&'arena Expr<'src, 'arena>>),
	GetRef(Loc<&'arena Expr<'src, 'arena>>),
	Deref(Loc<&'arena Expr<'src, 'arena>>),
	Sizeof(Loc<&'arena Ty<'src, 'arena>>)
}

#[derive(Debug, PartialEq)]
pub enum Stmt<'src, 'arena> where 'src: 'arena {
	Assign(Loc<Expr<'src, 'arena>>, Loc<Expr<'src, 'arena>>),
	Decl(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>),
	Return(Option<Loc<Expr<'src, 'arena>>>),
	SCall(Loc<&'src str>, &'arena [Loc<Expr<'src, 'arena>>]),
	GenericSCall{name: Loc<&'src str>, type_param: Loc<&'arena Ty<'src, 'arena>>, args: &'arena [Loc<Expr<'src, 'arena>>]},
	If(Loc<Expr<'src, 'arena>>, Block<'src, 'arena>, Block<'src, 'arena>),
	While(Expr<'src, 'arena>, Block<'src, 'arena>)
}

pub type Block<'src, 'arena> = &'arena [Loc<Stmt<'src, 'arena>>];

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum PolymorphMode{
	Separated,
	Erased
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

pub struct Func<'src: 'arena, 'arena> {
	pub ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
	pub name: Loc<&'src str>,
	pub args: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)],
	pub body: Block<'src, 'arena>,
}

pub struct Struct<'src: 'arena, 'arena> {
	pub name: Loc<&'src str>,
	pub fields: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)]
}

pub struct GenericStruct<'src: 'arena, 'arena> {
	pub name: Loc<&'src str>,
	pub var: Loc<&'src str>,
	pub fields: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)]
}

pub struct GenericFunc<'src: 'arena, 'arena> {
	pub ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
	pub name: Loc<&'src str>,
	pub args: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)],
	pub body: Block<'src, 'arena>,
	pub var: Loc<&'src str>,
}

pub struct ExternalFunc<'src: 'arena, 'arena> {
	pub name: Loc<&'src str>,
	pub ret_type: Loc<Option<&'arena Ty<'src, 'arena>>>,
	pub arg_types: &'arena [Loc<&'arena Ty<'src, 'arena>>]
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
	fn from_gdecls(gdecls: &[&'arena Gdecl<'src, 'arena>], arena: &'arena bumpalo::Bump) -> &'arena Self {
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
		let mut just_externs = gdecls.iter().filter_map(|g| {
			if let Extern{ret_type, name, arg_types} = g {
				Some(ExternalFunc{ name: *name, ret_type: *ret_type, arg_types })
			} else { None }
		});
		//just_externs isn't an ExactSizeIterator, so I can't use arena.alloc_slice_fill_iter()
		let external_funcs: &'arena [ExternalFunc<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_externs, |_| just_externs.next().unwrap());
		debug_assert!(just_externs.next().is_none(), "More externs than expected, num_externs = {}", num_externs);

		let mut just_globals = gdecls.iter().filter_map(|g| {
			if let GVarDecl(ty, name) = g {
				Some((*ty, *name))
			} else { None }
		});
		let global_vars: &'arena [(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)] =
			arena.alloc_slice_fill_with(num_globals, |_| just_globals.next().unwrap());
		debug_assert!(just_globals.next().is_none(), "More globals than expected, num_globals = {}", num_globals);

		let mut just_funcs = gdecls.iter().filter_map(|g| {
			if let GFuncDecl{ret_type, name, args, body} = g {
				Some(Func{ret_type: *ret_type, name: *name, args, body})
			} else { None }
		});
		let funcs: &'arena [Func<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_funcs, |_| just_funcs.next().unwrap());
		debug_assert!(just_funcs.next().is_none(), "More funcs than expected, num_funcs = {}", num_funcs);

		let mut just_structs = gdecls.iter().filter_map(|g| {
			if let GStructDecl{name, fields} = g {
				Some(Struct{name: *name, fields})
			} else { None }
		});
		let structs: &'arena [Struct<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_structs, |_| just_structs.next().unwrap());
		debug_assert!(just_structs.next().is_none(), "More structs than expected, num_structs = {}", num_structs);

		let mut just_erased_structs = gdecls.iter().filter_map(|g| {
			if let GGenericStructDecl{name, fields, var, mode: Loc{elt: PolymorphMode::Erased, ..}} = g {
				Some(GenericStruct{name: *name, var: *var, fields})
			} else { None }
		});
		let erased_structs: &'arena [GenericStruct<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_erased_structs, |_| just_erased_structs.next().unwrap());
		debug_assert!(just_erased_structs.next().is_none(), "More erased structs than expected, num_erased_structs = {}", num_erased_structs);

		let mut just_separated_structs = gdecls.iter().filter_map(|g| {
			if let GGenericStructDecl{name, fields, var, mode: Loc{elt: PolymorphMode::Separated, ..}} = g {
				Some(GenericStruct{name: *name, var: *var, fields})
			} else { None }
		});
		let separated_structs: &'arena [GenericStruct<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_separated_structs, |_| just_separated_structs.next().unwrap());
		debug_assert!(just_separated_structs.next().is_none(), "More separated structs than expected, num_separated_structs = {}", num_separated_structs);

		let mut just_erased_funcs = gdecls.iter().filter_map(|g| {
			if let GGenericFuncDecl{ret_type, name, args, body, var, mode: Loc{elt: PolymorphMode::Separated, ..}} = g {
				Some(GenericFunc{ret_type: *ret_type, name: *name, args, body, var: *var})
			} else { None }
		});
		let erased_funcs: &'arena [GenericFunc<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_erased_funcs, |_| just_erased_funcs.next().unwrap());
		debug_assert!(just_erased_funcs.next().is_none(), "More erased funcs than expected, num_erased_funcs = {}", num_erased_funcs);

		let mut just_separated_funcs = gdecls.iter().filter_map(|g| {
			if let GGenericFuncDecl{ret_type, name, args, body, var, mode: Loc{elt: PolymorphMode::Separated, ..}} = g {
				Some(GenericFunc{ret_type: *ret_type, name: *name, args, body, var: *var})
			} else { None }
		});
		let separated_funcs: &'arena [GenericFunc<'src, 'arena>] =
			arena.alloc_slice_fill_with(num_separated_funcs, |_| just_separated_funcs.next().unwrap());
		debug_assert!(just_separated_funcs.next().is_none(), "More separated funcs than expected, num_separated_funcs = {}", num_separated_funcs);

		let result_prog = Program {
			external_funcs,
			global_vars,
			funcs,
			structs,
			erased_structs,
			separated_structs,
			erased_funcs,
			separated_funcs
		};
		arena.alloc(result_prog)
	}
}
