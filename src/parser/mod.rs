#![allow(dead_code)]
use crate::ast2::*;

use crate::lexer::{Token, TokenLoc};
use crate::driver::Error;

/*uncomment this once there are parse tests
#[cfg(test)]
mod tests;
*/

//when parser is done, find largest argument to peek
const PARSE_MAX_PEEK: usize = 5;

//very similar Peeker in the lexer, but with a different constant for the size of the array, and iterates over tokens
struct Peeker<'src, T: Iterator<Item = TokenLoc<'src>>> {
	tokens: T,
	buf: [TokenLoc<'src>; PARSE_MAX_PEEK],
	next_read: u8,
	amount_buffered: u8
}
impl<'src, T: Iterator<Item = TokenLoc<'src>>> Peeker<'src, T> {
	fn new(tokens: T) -> Self {
		Peeker{
			tokens,
			buf: Default::default(),
			next_read: 0,
			amount_buffered: 0
		}
	}
	//amount is 0-indexed: peek(0) gets the very next token
	fn peek(&mut self, amount: u8) -> Option<TokenLoc<'src>> {
		debug_assert!((amount as usize) < PARSE_MAX_PEEK, "Cannot peek ahead {}, need to increase PARSE_MAX_PEEK (currently {})", amount, PARSE_MAX_PEEK);
		if amount < self.amount_buffered {
			return Some(self.buf[(self.next_read + amount) as usize % PARSE_MAX_PEEK].clone());
		}
		//the requested char is not buffered
		let mut insert_index: u8 = (self.next_read + self.amount_buffered) % PARSE_MAX_PEEK as u8;
		for i in 0..(amount - self.amount_buffered + 1) {
			let next_token = match self.tokens.next() {
				Some(c) => c,
				None => {
					self.amount_buffered += i;
					return None
				}
			};
			self.buf[insert_index as usize] = next_token;
			insert_index = (insert_index + 1) % PARSE_MAX_PEEK as u8;
		}
		self.amount_buffered = amount + 1;
		Some(self.buf[(self.next_read + amount) as usize % PARSE_MAX_PEEK].clone())
	}
}
impl<'src, T: Iterator<Item = TokenLoc<'src>>> Iterator for Peeker<'src, T> {
	type Item = TokenLoc<'src>;
	fn next(&mut self) -> Option<TokenLoc<'src>> {
		if self.amount_buffered == 0 {
			//nothing in buf, defer to base iterator
			self.tokens.next()
		} else {
			//ok to mem::take here because the buf slot will not be read again
			let result = std::mem::take(&mut self.buf[self.next_read as usize]);
			self.next_read = (self.next_read + 1) % PARSE_MAX_PEEK as u8;
			self.amount_buffered -= 1;
			Some(result)
		}
	}
}

pub struct Parser<'src: 'arena, 'arena, T: Iterator<Item = TokenLoc<'src>>> {
	peeker: Peeker<'src, T>,
	errors: Vec<Error>,
	file_id: u16,
	arena: &'arena bumpalo::Bump,
	typecache: &'arena TypeCache<'src, 'arena>,
	//when reporting a parse error due to EOF, I need a way to get the last seen byte offset
	latest_byte_offset: usize
}
/*
Gdecl = EXTERN <Ty or void> ID LPAREN Comma<Ty> RPAREN SEMI
	  | <Ty> ID SEMI
	  | <Ty or void> ID LPAREN Comma<Ty ID> RPAREN <Block>
	  | <Ty or void> ID AT LT (SEPARATED | ERASED) APOSTROPHE ID GT LPAREN Comma<Ty ID> RPAREN <Block>
	  | STRUCT ID LBRACE (<Ty> ID SEMI)* RBRACE
	  | STRUCT ID AT LR (SEPARATED | ERASED) APOSTROPHE ID GT LBRACE (<Ty> ID SEMI)* RBRACE

Block = LBRACE (<Stmt>)* RBRACE

Stmt = <Expr> EQ <Expr> SEMI
	 | <Ty> ID SEMI
	 | <Ty> ID EQ <Expr> SEMI //not in oldparser but shouldn't be that difficult to implement
	 | RETURN <Expr>? SEMI
	 | ID LPAREN Comma<Expr> RPAREN SEMI
	 | ID AT LT <Ty> GT LPAREN Comma<Expr> RPAREN SEMI
	 | WHILE <Expr> <Block>
	 | <IfStmt>
	 //these would require changing the lexer, or else parse_expr would always have to look ahead for an EQ
	 | <Expr> PLUSPLUS
	 | <Expr> MINUSMINUS
	 | <Expr> OPEQ <Expr>

IfStmt = IF <Expr> <Block> <ElseStmt>
ElseStmt =
		 | ELSE <Block>
		 | ELSE <IfStmt> 

Expr precedence:
||
&&
|
^
&
== !=
< <= > >=
<< >> >>>
+ -
* / %
& * ~ ! -
[index] sizeof() cast() call() genericcall() proj
literals identifiers parens

base Ty or void= BOOL
		| INTTYPE
		| F32
		| F64
		| VOID
		| STRUCT ID
		| STRUCT ID AT LT <Ty or void> GT
		| APOSTROPHE ID
Ty = <base Ty or void> (STAR | (LBRACKET INT RBRACKET))*
*/


//what to do to the parser's internal state when an error is encountered
#[derive(Debug, Clone)]
enum ErrorHandler<'src> {
	ConsumeIncluding(Token<'src>),
	Nothing,
}
impl<'src: 'arena, 'arena, T: Iterator<Item = TokenLoc<'src>>> Parser<'src, 'arena, T> {
	pub fn new(chunk_of_tokens: T, file_id: u16, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Self {
		let mut peeker = Peeker::new(chunk_of_tokens);
		let latest_byte_offset = peeker.peek(0).expect("empty chunk").byte_offset;
		Parser{
			peeker,
			errors: Vec::new(),
			file_id,
			arena,
			typecache,
			latest_byte_offset,
		}
	}
	//if the next token is of the same variant as any of the candidates, returns true
	fn next_in(&mut self, candidates: &[Token<'src>]) -> Option<TokenLoc<'src>> {
		match self.peeker.peek(0) {
			None => None,
			Some(next_tok) => {
				for token in candidates.iter() {
					if next_tok.token.same_kind(token) {
						self.poll();
						return Some(next_tok);
					}
				}
				None
			}
		}
	}
	fn poll(&mut self) -> Option<TokenLoc<'src>> {
		match self.peeker.next() {
			None => None,
			Some(t) => {
				self.latest_byte_offset = t.byte_offset;
				Some(t)
			}
		}
	}
	fn located<EltType>(&self, elt: EltType, data: TokenLoc<'src>) -> Loc<EltType> {
		Loc{
			elt,
			byte_offset: data.byte_offset,
			byte_len: data.byte_len,
			file_id: self.file_id
		}
	}
	pub fn parse_gdecls(mut self) -> (Vec<&'arena Gdecl<'src, 'arena>>, Vec<Error>) {
		use Token::*;
		let mut result = Vec::new();
		self.parse_ty(&ErrorHandler::ConsumeIncluding(SEMI)).map(|t_loc| {
			if let Some(TokenLoc{token: IDENT(varname), byte_offset, byte_len}) = self.expect(Some(&IDENT("")), &ErrorHandler::ConsumeIncluding(SEMI), "a name for global variable") {
				let gdecl = Gdecl::GVarDecl(t_loc, Loc{elt: varname, byte_offset, byte_len, file_id: self.file_id});
				result.push(&*self.arena.alloc(gdecl));
				self.expect(Some(&SEMI), &ErrorHandler::Nothing, "';' after global variable");
			}
			//did not find name for global var, already consumed next ;, don't need to do anything
		});
		(result, self.errors)
		
		/*
		let first_3_tokens: Vec<_> = self.peeker.take(3).collect();
		dbg!(&first_3_tokens);
		self.errors.push(Error{
			err: "first bad token".to_owned(),
			byte_offset: first_3_tokens[0].byte_offset,
			approx_len: first_3_tokens[0].byte_len,
			file_id: self.file_id
		});
		self.errors.push(Error{
			err: "second and third bad tokens".to_owned(),
			byte_offset: first_3_tokens[1].byte_offset,
			approx_len: first_3_tokens[2].byte_offset - first_3_tokens[1].byte_offset + first_3_tokens[2].byte_len,
			file_id: self.file_id
		});
		let ty = Ty::Bool.getref(self.typecache);
		let ty_loc = Loc{elt: ty, byte_offset: first_3_tokens[2].byte_offset, byte_len: 0, file_id: self.file_id};
		let name = &*Box::leak(format!("file_{}", self.file_id).into_boxed_str());
		let name_loc = Loc{elt: name, byte_offset: 0, byte_len: 0, file_id: self.file_id};
		let temp = &*self.arena.alloc(Gdecl::GVarDecl(ty_loc, name_loc));
		(vec![temp], self.errors)
		*/
	}
	//executes the given error recovery method
	fn handle_error(&mut self, method: &ErrorHandler<'src>) -> bool {
		use ErrorHandler::*;
		match method {
			ConsumeIncluding(token) => {
				loop {
					match self.poll() {
						None => return false,
						Some(t) if t.token.same_kind(token) => return true,
						Some(_) => ()
					}
				}
			},
			Nothing => true
		}
	}
	//if the next token has the same kind as the provided kind, consume it. otherwise, report an error. Can be called with None
	//as the token_kind if no token kinds are acceptable.
	fn expect<E: std::fmt::Display>(&mut self, token_kind: Option<&Token<'src>>, error_handler: &ErrorHandler<'src>, expected: E) -> Option<TokenLoc<'src>> {
		match self.peeker.peek(0) {
			Some(next_loc) if token_kind.is_some() && next_loc.token.same_kind(token_kind.unwrap()) => self.poll(),
			Some(next_loc) => {
				self.errors.push(Error{
					err: format!("Expected {}, found {}", expected, next_loc.token),
					byte_offset: next_loc.byte_offset,
					approx_len: next_loc.byte_len,
					file_id: self.file_id
				});
				self.handle_error(error_handler);
				None
			},
			None => {
				self.errors.push(Error{
					err: format!("Expected {}, found EOF", expected),
					byte_offset: self.latest_byte_offset,
					approx_len: 0,
					file_id: self.file_id
				});
				self.handle_error(error_handler);
				None
			}
		}
	}
	fn parse_base_ty_or_void(&mut self, error_handler: &ErrorHandler<'src>) -> Option<Loc<Option<&'arena Ty<'src, 'arena>>>> {
		use Token::*;
		let next_loc_if_base_ty = self.next_in(&[BOOL, INTTYPE{bits: IntSize::Size8, signed: false}, F32, F64, VOID, STRUCT, APOSTROPHE]);
		match next_loc_if_base_ty.as_ref().map(|x| &x.token) {
			Some(BOOL) => return Some(self.located(Some(Ty::Bool.getref(self.typecache)), next_loc_if_base_ty.unwrap())),
			Some(INTTYPE{bits, signed}) => return Some(self.located(Some(Ty::Int{signed: *signed, size: *bits}.getref(self.typecache)), next_loc_if_base_ty.unwrap())),
			Some(F32) => return Some(self.located(Some(Ty::Float(FloatSize::FSize32).getref(self.typecache)), next_loc_if_base_ty.unwrap())),
			Some(F64) => return Some(self.located(Some(Ty::Float(FloatSize::FSize64).getref(self.typecache)), next_loc_if_base_ty.unwrap())),
			Some(VOID) => return Some(self.located(None, next_loc_if_base_ty.unwrap())),
			Some(STRUCT) => {
				match self.expect(Some(&IDENT("")), error_handler, "a struct name")? {
					TokenLoc{token: IDENT(struct_name), byte_offset, byte_len} => {
						if self.next_in(&[AT]).is_some() {
							self.expect(Some(&LT), error_handler, "<")?;
							let type_param_loc = self.parse_ty(error_handler)?;
							let gt_loc = self.expect(Some(&GT), error_handler, ">")?;
							let elt = Ty::GenericStruct{type_param: type_param_loc.elt, name: struct_name}.getref(self.typecache);
							let begin_offset = next_loc_if_base_ty.unwrap().byte_offset;
							return Some(Loc{
								elt: Some(elt),
								byte_offset: begin_offset,
								byte_len: gt_loc.byte_offset - begin_offset + gt_loc.byte_len,
								file_id: self.file_id
							});
						} else {
							let elt = Ty::Struct(struct_name).getref(self.typecache);
							let begin_offset = next_loc_if_base_ty.unwrap().byte_offset;
							return Some(Loc{
								elt: Some(elt),
								byte_offset: begin_offset,
								byte_len: byte_offset - begin_offset + byte_len,
								file_id: self.file_id
							});
						}
					},
					_ => unreachable!(),
				};
			},
			Some(APOSTROPHE) => {
				match self.expect(Some(&IDENT("")), error_handler, "a type variable")? {
					TokenLoc{token: IDENT(type_var), byte_offset: ident_offset, byte_len: ident_len} => {
						let elt = Ty::TypeVar(type_var).getref(self.typecache);
						let apos_offset = next_loc_if_base_ty.unwrap().byte_offset;
						return Some(Loc{
							elt: Some(elt),
							byte_offset: apos_offset,
							byte_len: ident_offset - apos_offset + ident_len,
							file_id: self.file_id
						});
					}
					_ => unreachable!(),
				};
			}
			Some(other) => panic!("{:?} is not a base ty", other),
			None => ()
		};
		//base ty or void not found, now diagnose the error
		self.expect(None, error_handler, "a type");
		None
	}
	fn parse_ty_or_void(&mut self, error_handler: &ErrorHandler<'src>) -> Option<Loc<Option<&'arena Ty<'src, 'arena>>>> {
		use Token::*;
		let Loc{elt: mut base_ty, byte_offset: initial_offset, byte_len: mut last_len, ..} = self.parse_base_ty_or_void(error_handler)?;
		let mut last_offset = initial_offset;
		loop {
			match self.next_in(&[STAR, LBRACKET]) {
				None => return Some(Loc{
					elt: base_ty,
					byte_offset: initial_offset,
					byte_len: last_offset - initial_offset + last_len,
					file_id: self.file_id
				}),
				Some(TokenLoc{token: STAR, byte_offset: star_offset, byte_len: star_len, ..}) => {
					base_ty = Some(Ty::Ptr(base_ty).getref(self.typecache));
					last_offset = star_offset;
					last_len = star_len;
				},
				Some(TokenLoc{token: LBRACKET, ..}) => {
					let array_len_tok = self.expect(Some(&INT{val: 0, bits: IntSize::Size8, signed: true}), error_handler, "an array length")?;
					let array_len = match array_len_tok.token {
						INT{val, ..} => val,
						_ => unreachable!()
					};
					let rbracket_loc = self.expect(Some(&RBRACKET), error_handler, "]")?;
					last_offset = rbracket_loc.byte_offset;
					last_len = rbracket_loc.byte_len;
					if let Some(nonvoid) = base_ty {
						base_ty = Some(Ty::Array{typ: nonvoid, length: array_len}.getref(self.typecache));
					} else {
						self.errors.push(Error{
							err: "The base type of an array cannot be void".to_owned(),
							byte_offset: initial_offset,
							approx_len: last_offset - initial_offset + last_len,
							file_id: self.file_id
						});
						self.handle_error(error_handler);
						return None;
					}
				},
				Some(_) => unreachable!()
			}
		}
	}
	fn parse_ty(&mut self, error_handler: &ErrorHandler<'src>) -> Option<Loc<&'arena Ty<'src, 'arena>>> {
		//call parse_ty_or_void, report an error if it is void
		match self.parse_ty_or_void(error_handler)? {
			Loc{elt: None, byte_offset, byte_len, ..} => {
				self.errors.push(Error{
					err: "Expected a type, found void".to_owned(),
					byte_offset,
					approx_len: byte_len,
					file_id: self.file_id
				});
				self.handle_error(error_handler);
				None
			},
			Loc{elt: Some(t), byte_offset, byte_len, ..} => {
				Some(Loc{
					elt: t,
					byte_offset, byte_len, file_id: self.file_id
				})
			}
		}
	}
}
