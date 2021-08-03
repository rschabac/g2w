#![allow(dead_code)]
use crate::ast2::*;

use crate::lexer::{Token, TokenLoc};
use Token::*;
use crate::driver::Error;

#[cfg(test)]
mod tests;

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
	 | RETURN <Expr>? SEMI
	 | ID LPAREN Comma<Expr> RPAREN SEMI
	 | ID AT LT <Ty> GT LPAREN Comma<Expr> RPAREN SEMI
	 | WHILE <Expr> <Block>
	 | <IfStmt>
	 //these would require changing the lexer, or else parse_expr would always have to look ahead for an EQ
	 | <Expr> PLUSPLUS
	 | <Expr> MINUSMINUS
	 | <Expr> OPEQ <Expr>
	 //would be easiest to do this by changing the Stmt enum in ast2
	 | <Ty> ID EQ <Expr> SEMI //not in oldparser but shouldn't be that difficult to implement

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

const CAN_START_TY: &[Token<'static>] = &[BOOL, INTTYPE{bits: IntSize::Size8, signed: false}, F32, F64, VOID, STRUCT, APOSTROPHE];
const CAN_START_BASE_EXPR: &[Token<'static>] = &[NULL, TRUE, FALSE, INT{val: 0, bits: IntSize::Size8, signed: false}, FLOAT{val: 0.0, bits: FloatSize::FSize32}, STR(std::borrow::Cow::Borrowed("")), IDENT(""), SIZEOF, CAST, LPAREN, AND, STAR, TILDE, NOT, MINUS];
const OPERATORS: &[Token<'static>] = &[LBRACKET, DOT, LT, LTE, GT, GTE, EQEQ, NOTEQ, OR, OROR, AND, ANDAND, XOR, SHL, SHR, SAR, PLUS, MINUS, STAR, SLASH, PERCENT];

//what to do to the parser's internal state when an error is encountered
#[derive(Debug, Clone)]
pub enum ErrorHandler<'src> {
	ConsumeIncluding(Token<'src>),
	Nothing,
	UntilBalanced,
	UntilEndOfChainedIf,
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
	//if the next token is of the same variant as any of the candidates, returns it
	fn next_in(&mut self, candidates: &[Token<'src>]) -> Option<TokenLoc<'src>> {
		self.expect::<&str>(candidates, &ErrorHandler::Nothing, None)
	}
	//if the next token has the same kind as the provided kind, consume it. otherwise, report an error. Can be called with &[]
	//as the token_kind if no token kinds are acceptable. if expected is Some(_), emit an error message.
	fn expect<E: std::fmt::Display>(&mut self, token_kinds: &[Token<'src>], error_handler: &ErrorHandler<'src>, expected: Option<E>) -> Option<TokenLoc<'src>> {
		match self.peeker.peek(0) {
			Some(next_loc) if token_kinds.iter().any(|t| t.same_kind(&next_loc.token)) => self.poll(),
			Some(next_loc) => {
				if let Some(expected) = expected {
					self.errors.push(Error{
						//TODO: change Display impl for Token, enhance this error message
						err: format!("Expected {}, found {}", expected, next_loc.token),
						byte_offset: next_loc.byte_offset,
						approx_len: next_loc.byte_len,
						file_id: self.file_id
					});
				}
				self.handle_error(error_handler);
				None
			},
			None => {
				if let Some(expected) = expected {
					self.errors.push(Error{
						err: format!("Expected {}, found end of parsing chunk (either end of file or too many closing braces)", expected),
						byte_offset: self.latest_byte_offset,
						approx_len: 0,
						file_id: self.file_id
					});
				}
				self.handle_error(error_handler);
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
	fn located<EltType>(&self, elt: EltType, data: &TokenLoc<'src>) -> Loc<EltType> {
		Loc{
			elt,
			byte_offset: data.byte_offset,
			byte_len: data.byte_len,
			file_id: self.file_id
		}
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
			Nothing => true,
			UntilBalanced => {
				let mut balance = 0;
				let mut result = false;
				while let Some(tokenloc) = self.poll() {
					if tokenloc.token == LBRACE {
						balance += 1;
					} else if tokenloc.token == RBRACE {
						balance -= 1;
						if balance == 0 {
							result = true;
							break;
						}
					}
				}
				result
			},
			//if there is an error parsing the condition of an if stmt, skip until balanced, then check if the next token is ELSE,
			//if it is, then consume the whole else branch. repeat as many times as necessary.
			UntilEndOfChainedIf => {
				if !self.handle_error(&UntilBalanced) {
					return false;
				}
				while self.peeker.peek(0).map(|t| t.token) == Some(ELSE) {
					if !self.handle_error(&UntilBalanced) {
						return false;
					}
				}
				true
			}
		}
	}
	fn id_token_loc_to_loc(&self, token_loc: &TokenLoc<'src>) -> Loc<&'src str> {
		Loc{
			elt: match token_loc.token {
				IDENT(s) => s,
				_ => unreachable!()
			},
			byte_offset: token_loc.byte_offset, byte_len: token_loc.byte_len, file_id: self.file_id
		}
	}
	fn parse_base_ty_or_void(&mut self, error_handler: &ErrorHandler<'src>) -> Option<Loc<Option<&'arena Ty<'src, 'arena>>>> {
		let next_loc_if_base_ty = self.next_in(CAN_START_TY);
		match next_loc_if_base_ty.as_ref().map(|x| &x.token) {
			Some(BOOL) => return Some(self.located(Some(Ty::Bool.getref(self.typecache)), &next_loc_if_base_ty.unwrap())),
			Some(INTTYPE{bits, signed}) => return Some(self.located(Some(Ty::Int{signed: *signed, size: *bits}.getref(self.typecache)), &next_loc_if_base_ty.unwrap())),
			Some(F32) => return Some(self.located(Some(Ty::Float(FloatSize::FSize32).getref(self.typecache)), &next_loc_if_base_ty.unwrap())),
			Some(F64) => return Some(self.located(Some(Ty::Float(FloatSize::FSize64).getref(self.typecache)), &next_loc_if_base_ty.unwrap())),
			Some(VOID) => return Some(self.located(None, &next_loc_if_base_ty.unwrap())),
			Some(STRUCT) => {
				match self.expect(&[IDENT("")], error_handler, Some("a struct name"))? {
					TokenLoc{token: IDENT(struct_name), byte_offset, byte_len} => {
						if self.next_in(&[AT]).is_some() {
							self.expect(&[LT], error_handler, Some("'<'"))?;
							let type_param_loc = self.parse_ty(error_handler)?;
							let gt_loc = self.expect(&[GT], error_handler, Some("'>'"))?;
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
				match self.expect(&[IDENT("")], error_handler, Some("a type variable"))? {
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
		self.expect(&[], error_handler, Some("a type"));
		None
	}
	fn parse_ty_or_void(&mut self, error_handler: &ErrorHandler<'src>) -> Option<Loc<Option<&'arena Ty<'src, 'arena>>>> {
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
					let array_len_tok = self.expect(&[INT{val: 0, bits: IntSize::Size8, signed: true}], error_handler, Some("an array length"))?;
					let array_len = match array_len_tok.token {
						INT{val, ..} => val,
						_ => unreachable!()
					};
					let rbracket_loc = self.expect(&[RBRACKET], error_handler, Some("']'"))?;
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
	pub fn parse_ty(&mut self, error_handler: &ErrorHandler<'src>) -> Option<Loc<&'arena Ty<'src, 'arena>>> {
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
	//doesn't call self.handle_error, but does report the error
	fn parse_expr_without_handling_error(&mut self, prec_level: i32) -> Option<Loc<Expr<'src, 'arena>>> {
		let first_expr_loc = match self.peeker.peek(0) {
			None => {
				self.errors.push(Error{
					err: "Expected 'null', 'true', 'false', 'sizeof', 'cast', '(', '&', '*', '~', '!', '-', or a number or string literal, but found end of parsing chunk (either end of file or too many closing braces)".to_owned(),
					byte_offset: self.latest_byte_offset,
					approx_len: 0,
					file_id: self.file_id
				});
				None
			},
			Some(next_tok) => {
				let cloned = next_tok.clone();
				let mut result = None;
				for token in CAN_START_BASE_EXPR.iter() {
					if next_tok.token.same_kind(token) {
						self.poll();
						result = Some(next_tok);
						break;
					}
				}
				if result.is_none() {
					let next_tok = cloned;
					self.errors.push(Error{
						err: format!("Expected 'null', 'true', 'false', 'sizeof', 'cast', '(', '&', '*', '~', '!', '-', or a number or string literal, but found {}", next_tok.token),
						byte_offset: next_tok.byte_offset,
						approx_len: next_tok.byte_len,
						file_id: self.file_id
					});
				}
				result
			}
		}?;
		let mut lhs: Loc<Expr<'src, 'arena>> = match &first_expr_loc.token {
			NULL => self.located(Expr::LitNull, &first_expr_loc),
			TRUE | FALSE => self.located(Expr::LitBool(first_expr_loc.token == TRUE), &first_expr_loc),
			INT{val, bits, signed: true} => self.located(Expr::LitSignedInt(*val as i64, *bits), &first_expr_loc),
			INT{val, bits, signed: false} => self.located(Expr::LitUnsignedInt(*val, *bits), &first_expr_loc),
			FLOAT{val, bits} => self.located(Expr::LitFloat(*val, *bits), &first_expr_loc),
			STR(s) => self.located(Expr::LitString(s.clone()), &first_expr_loc),
			IDENT(id) => {
				//try to parse a function call
				let call_result = self.parse_call(&first_expr_loc, &ErrorHandler::Nothing);
				if let Some(call_expr) = call_result? {
					call_expr
				} else {
					self.located(Expr::Id(id), &first_expr_loc)
				}
			},
			SIZEOF => {
				self.expect(&[LPAREN], &ErrorHandler::Nothing, Some("'('"))?;
				let ty_loc = self.parse_ty(&ErrorHandler::Nothing)?;
				let rparen_loc = self.expect(&[RPAREN], &ErrorHandler::Nothing, Some("')'"))?;
				Loc{
					byte_offset: first_expr_loc.byte_offset,
					byte_len: rparen_loc.byte_offset - first_expr_loc.byte_offset + rparen_loc.byte_len,
					elt: Expr::Sizeof(ty_loc),
					file_id: self.file_id
				}
			},
			CAST => {
				self.expect(&[LPAREN], &ErrorHandler::Nothing, Some("'('"))?;
				let ty_loc = self.parse_ty(&ErrorHandler::Nothing)?;
				self.expect(&[COMMA], &ErrorHandler::Nothing, Some("','"))?;
				let nested_loc = self.parse_expr(&ErrorHandler::Nothing)?;
				let rparen_loc = self.expect(&[RPAREN], &ErrorHandler::Nothing, Some("')'"))?;
				Loc{
					byte_offset: first_expr_loc.byte_offset,
					byte_len: rparen_loc.byte_offset - first_expr_loc.byte_offset + rparen_loc.byte_len,
					elt: Expr::Cast(ty_loc, nested_loc.alloc(self.arena)),
					file_id: self.file_id
				}
			},
			AND | STAR | TILDE | MINUS | NOT => {
				let unop = &first_expr_loc.token;
				//recurse with prec_level = 110, greater than any binop precedence
				let operand_loc = self.parse_expr_without_handling_error(110)?.alloc(self.arena);
				let result_expr = match unop {
					AND => Expr::GetRef(operand_loc),
					STAR => Expr::Deref(operand_loc),
					TILDE => Expr::Unop(UnaryOp::Bitnot, operand_loc),
					MINUS => Expr::Unop(UnaryOp::Neg, operand_loc),
					NOT => Expr::Unop(UnaryOp::Lognot, operand_loc),
					_ => unreachable!()
				};
				Loc{
					byte_offset: first_expr_loc.byte_offset,
					byte_len: operand_loc.byte_offset - first_expr_loc.byte_offset + operand_loc.byte_len,
					elt: result_expr,
					file_id: self.file_id
				}
			},
			LPAREN => {
				let nested_loc = self.parse_expr(&ErrorHandler::Nothing)?;
				let rparen_loc = self.expect(&[RPAREN], &ErrorHandler::Nothing, Some("')'"))?;
				Loc{
					byte_offset: first_expr_loc.byte_offset,
					byte_len: rparen_loc.byte_offset - first_expr_loc.byte_offset + rparen_loc.byte_len,
					elt: nested_loc.elt,
					file_id: self.file_id
				}
			},
			_ => unreachable!()
		};
		loop {
			let next_tok_loc = self.peeker.peek(0);
			//if the next token is not one of these, return the current lhs
			let next_tok_loc = match next_tok_loc {
				None => break,
				Some(t) if OPERATORS.iter().any(|token| token.same_kind(&t.token)) => t,
				Some(_) => break,
			};
			if next_tok_loc.token == LBRACKET {
				self.poll();
				let index_loc = self.parse_expr(&ErrorHandler::Nothing)?;
				let rbracket_loc = self.expect(&[RBRACKET], &ErrorHandler::Nothing, Some("]"))?;
				lhs = Loc{
					byte_offset: lhs.byte_offset,
					byte_len: rbracket_loc.byte_offset - lhs.byte_offset + rbracket_loc.byte_len,
					elt: Expr::Index(lhs.alloc(self.arena), index_loc.alloc(self.arena)),
					file_id: self.file_id
				};
				continue;
			}
			if next_tok_loc.token == DOT {
				self.poll();
				let field_loc: TokenLoc<'_> = self.expect(&[IDENT("")], &ErrorHandler::Nothing, Some("a struct field name"))?;
				let field_loc: Loc<_> = self.id_token_loc_to_loc(&field_loc);
				lhs = Loc{
					byte_offset: lhs.byte_offset,
					byte_len: field_loc.byte_offset - lhs.byte_offset + field_loc.byte_len,
					elt: Expr::Proj(lhs.alloc(self.arena), field_loc),
					file_id: self.file_id
				};
				continue;
			}

			let (this_op_prec, binop) = next_tok_loc.token.precedence();
			if this_op_prec <= prec_level {
				break;
			}
			self.poll(); //only consume the operator once I've checked it's precedence
			let rhs = self.parse_expr_without_handling_error(this_op_prec)?;
			lhs = Loc{
				byte_offset: lhs.byte_offset,
				byte_len: rhs.byte_offset - lhs.byte_offset + rhs.byte_len,
				elt: Expr::Binop(lhs.alloc(self.arena), binop, rhs.alloc(self.arena)),
				file_id: self.file_id
			};
		}
		Some(lhs)
	}
	pub fn parse_expr(&mut self, error_handler: &ErrorHandler<'src>) -> Option<Loc<Expr<'src, 'arena>>> {
		let expr_opt = self.parse_expr_without_handling_error(i32::MIN);
		if expr_opt.is_none() {
			self.handle_error(error_handler);
		}
		expr_opt
	}
	//returns None if there was an error, Some(None) if there was no function call, just an expr, Some(Some(Call)) if there was a call
	fn parse_call(&mut self, name_loc: &TokenLoc<'src>, error_handler: &ErrorHandler<'src>) -> Option<Option<Loc<Expr<'src, 'arena>>>> {
		let mut type_param: Option<Loc<&'arena Ty<'src, 'arena>>> = None;
		let name_loc = self.id_token_loc_to_loc(name_loc);
		if self.next_in(&[AT]).is_some() {
			self.expect(&[LT], error_handler, Some("'<'"))?;
			let ty_loc = self.parse_ty(error_handler)?;
			self.expect(&[GT], error_handler, Some("'>'"))?;
			type_param = Some(ty_loc);
			//after seeing '@<ty>', there must be an lparen
			self.expect(&[LPAREN], error_handler, Some("'('"))?;
		} else if self.next_in(&[LPAREN]).is_some() {
			//saw and consumed an lparen, non-generic call
		} else {
			//no lparen, the ident seen must just be an Id
			return Some(None);
		}
		let mut args: Vec<Loc<Expr<'_, '_>>> = Vec::new();
		let rparen_loc = match self.next_in(&[RPAREN]) {
			Some(l) => l,
			None => loop {
				args.push(self.parse_expr(error_handler)?);
				//if there is a comma, consume it, otherwise expect a ')'
				if self.next_in(&[COMMA]).is_none() {
					break self.expect(&[RPAREN], error_handler, Some("')'"))?
				}
			}
		};
		let args = if args.is_empty() {&[]} else {&*self.arena.alloc_slice_fill_iter(args.into_iter())};
		let result = if let Some(type_param_loc) = type_param {
			Expr::GenericCall{
				name: name_loc,
				type_param: type_param_loc,
				args
			}
		} else {
			Expr::Call(name_loc, args)
		};
		Some(Some(Loc{
			byte_offset: name_loc.byte_offset,
			byte_len: rparen_loc.byte_offset - name_loc.byte_offset + rparen_loc.byte_len,
			file_id: self.file_id,
			elt: result
		}))
	}
	pub fn parse_stmt(&mut self) -> Option<Loc<Stmt<'src, 'arena>>> {
		let next_token_can_start_ty = match self.peeker.peek(0) {
			None => false,
			Some(next) => CAN_START_TY.iter().any(|t| next.token.same_kind(t))
		};
		if next_token_can_start_ty {
			//must be a Decl
			let base_ty: Loc<_> = self.parse_ty(&ErrorHandler::ConsumeIncluding(SEMI))?;
			let varname = self.expect(&[IDENT("")], &ErrorHandler::ConsumeIncluding(SEMI), Some("a variable name"))?;
			let var_loc = self.id_token_loc_to_loc(&varname);
			let semi_loc_opt = self.expect(&[SEMI], &ErrorHandler::Nothing, Some(format_args!("a ';' after declaration of '{}'", var_loc.elt)));
			let semi_loc = match semi_loc_opt {
				None => {
					if self.next_in(&[EQ]).is_some() {
						self.errors.last_mut().unwrap().err.push_str("\nAssigning to a variable when declaring it is not yet implemented");
						self.handle_error(&ErrorHandler::ConsumeIncluding(SEMI));
					}
					return None;
				},
				Some(l) => l
			};
			return Some(Loc{
				byte_offset: base_ty.byte_offset,
				byte_len: semi_loc.byte_offset - base_ty.byte_offset + semi_loc.byte_len,
				file_id: self.file_id,
				elt: Stmt::Decl(base_ty, var_loc)
			});
		}
		if let Some(return_loc) = self.next_in(&[RETURN]) {
			if let Some(semi_loc) = self.next_in(&[SEMI]) {
				//returning nothing
				return Some(Loc{
					byte_offset: return_loc.byte_offset,
					byte_len: semi_loc.byte_offset - return_loc.byte_offset + semi_loc.byte_len,
					file_id: self.file_id,
					elt: Stmt::Return(None)
				});
			}
			//there should be an expr after this
			let retval_loc: Loc<_> = self.parse_expr(&ErrorHandler::ConsumeIncluding(SEMI))?;
			let semi_loc = self.expect(&[SEMI], &ErrorHandler::Nothing, Some("a ';' after return value"))?;
			return Some(Loc{
				byte_offset: return_loc.byte_offset,
				byte_len: semi_loc.byte_offset - return_loc.byte_offset + semi_loc.byte_len,
				file_id: self.file_id,
				elt: Stmt::Return(Some(retval_loc))
			});
		}
		if let Some(while_loc) = self.next_in(&[WHILE]) {
			let cond_loc = self.parse_expr(&ErrorHandler::UntilBalanced)?;
			let block: Loc<_> = self.parse_block(&ErrorHandler::UntilBalanced)?;
			return Some(Loc{
				byte_offset: while_loc.byte_offset,
				byte_len: block.byte_offset - while_loc.byte_offset + block.byte_len,
				file_id: self.file_id,
				elt: Stmt::While(cond_loc, block.elt)
			});
		}
		if let Some(if_loc) = self.next_in(&[IF]) {
			return self.parse_if_stmt(if_loc.byte_offset);
		}
		//must be either an assignment or a function call
		let lhs_or_call = self.parse_expr(&ErrorHandler::ConsumeIncluding(SEMI))?;
		if matches!(&lhs_or_call.elt, Expr::Call(_,_) | Expr::GenericCall{..}) {
			//this could still be an assignment. assigning to a function call should be caught in the typechecker, not here.
			if self.next_in(&[EQ]).is_some() {
				let rhs_loc = self.parse_expr(&ErrorHandler::ConsumeIncluding(SEMI))?;
				let semi_loc = self.expect(&[SEMI], &ErrorHandler::Nothing, Some("a ';' after assignment"))?;
				return Some(Loc{
					byte_offset: lhs_or_call.byte_offset,
					byte_len: semi_loc.byte_offset - lhs_or_call.byte_offset + semi_loc.byte_len,
					file_id: self.file_id,
					elt: Stmt::Assign(lhs_or_call, rhs_loc)
				});
			}
			//not an assignment, just a call
			let call = match lhs_or_call.elt {
				Expr::Call(name, args) => Stmt::SCall(name, args),
				Expr::GenericCall{name, type_param, args} => Stmt::GenericSCall{name, type_param, args},
				_ => unreachable!()
			};
			let semi_loc = self.expect(&[SEMI], &ErrorHandler::Nothing, Some("a ';' after assignment"))?;
			return Some(Loc{
				byte_offset: lhs_or_call.byte_offset,
				byte_len: semi_loc.byte_offset - lhs_or_call.byte_offset + semi_loc.byte_len,
				file_id: self.file_id,
				elt: call
			});
		}
		//lhs is not a call, this stmt must be an assignment
		self.expect(&[EQ], &ErrorHandler::ConsumeIncluding(SEMI), Some("a '=' after left-hand-side of assignment"))?;
		let rhs_loc = self.parse_expr(&ErrorHandler::ConsumeIncluding(SEMI))?;
		let semi_loc = self.expect(&[SEMI], &ErrorHandler::Nothing, Some("a ';' after assignment"))?;
		return Some(Loc{
			byte_offset: lhs_or_call.byte_offset,
			byte_len: semi_loc.byte_offset - lhs_or_call.byte_offset + semi_loc.byte_len,
			file_id: self.file_id,
			elt: Stmt::Assign(lhs_or_call, rhs_loc)
		});
	}
	//this method assumes that the IF token has already been consumed.
	fn parse_if_stmt(&mut self, if_offset: usize) -> Option<Loc<Stmt<'src, 'arena>>> {
		let cond_loc = self.parse_expr(&ErrorHandler::UntilEndOfChainedIf)?;
		let if_block = self.parse_block(&ErrorHandler::UntilEndOfChainedIf)?;
		let else_block = self.parse_else_stmt()?;
		Some(Loc{
			byte_offset: if_offset,
			byte_len: else_block.byte_offset - if_offset + else_block.byte_len,
			file_id: self.file_id,
			elt: Stmt::If(cond_loc, if_block.elt, else_block.elt)
		})
	}
	fn parse_else_stmt(&mut self) -> Option<Loc<Block<'src, 'arena>>> {
		if self.next_in(&[ELSE]).is_some() {
			if let Some(if_loc) = self.next_in(&[IF]) {
				let if_stmt = self.parse_if_stmt(if_loc.byte_offset)?;
				Some(Loc{
					byte_offset: if_loc.byte_offset,
					byte_len: if_stmt.byte_offset - if_loc.byte_offset + if_stmt.byte_len,
					file_id: self.file_id,
					elt: Block(std::slice::from_ref(&*self.arena.alloc(if_stmt)))
				})
			} else {
				self.parse_block(&ErrorHandler::UntilBalanced)
			}
		} else {
			Some(Loc{
				elt: Block(&[]),
				byte_offset: self.latest_byte_offset,
				byte_len: 1,
				file_id: self.file_id
			})
		}
	}
	//if an error is encountered, skips ahead to the closing brace
	fn parse_block(&mut self, error_handler: &ErrorHandler<'src>) -> Option<Loc<Block<'src, 'arena>>> {
		let lbrace_loc = self.expect(&[LBRACE], error_handler, Some("a '{' to begin a block"))?;
		let mut stmts: Vec<Loc<Stmt<'src, 'arena>>> = Vec::new();
		while self.peeker.peek(0).map(|t| t.token) != Some(RBRACE) {
			if let Some(stmt_loc) = self.parse_stmt() {
				stmts.push(stmt_loc);
			}
		}
		let rbrace_loc = self.expect(&[RBRACE], error_handler, Some("a '}' to close a block"))?;
		Some(Loc{
			elt: Block(&*self.arena.alloc_slice_fill_iter(stmts.into_iter())),
			byte_offset: lbrace_loc.byte_offset,
			byte_len: rbrace_loc.byte_offset - lbrace_loc.byte_offset + rbrace_loc.byte_len,
			file_id: self.file_id
		})
	}
	pub fn parse_gdecl(&mut self) -> Option<&'arena Gdecl<'src, 'arena>> {
		if self.next_in(&[EXTERN]).is_some() {
			let ret_ty_loc = self.parse_ty_or_void(&ErrorHandler::ConsumeIncluding(SEMI))?;
			let name_token_loc = self.expect(&[IDENT("")], &ErrorHandler::ConsumeIncluding(SEMI), Some("a name for this extern declaration"))?;
			let name_loc = self.id_token_loc_to_loc(&name_token_loc);
			self.expect(&[LPAREN], &ErrorHandler::ConsumeIncluding(SEMI), Some("'('"))?;
			let mut types = Vec::new();
			let _rparen_loc = match self.next_in(&[RPAREN]) {
				Some(l) => l,
				None => loop {
					types.push(self.parse_ty(&ErrorHandler::ConsumeIncluding(SEMI))?);
					//if there is a comma, consume it, otherwise expect a ')'
					if self.next_in(&[COMMA]).is_none() {
						break self.expect(&[RPAREN], &ErrorHandler::ConsumeIncluding(SEMI), Some("')'"))?
					}
				}
			};
			self.expect(&[SEMI], &ErrorHandler::Nothing, Some("a ';' after extern declaration"))?;
			let types = if types.is_empty() {&[]} else {&*self.arena.alloc_slice_fill_iter(types.into_iter())};
			return Some(&*self.arena.alloc(Gdecl::Extern{
				ret_type: ret_ty_loc,
				name: name_loc,
				arg_types: types
			}));
		}
		let first_type_loc = if let Some(struct_loc) = self.next_in(&[STRUCT]) {
			//could be a struct declaration, or the return type of a function
			//try to parse it as a return type, but return early if it turns out to be a struct declaration
			let name_token_loc = self.expect(&[IDENT("")], &ErrorHandler::UntilBalanced, Some("a struct name"))?;
			let name_loc = self.id_token_loc_to_loc(&name_token_loc);
			let mut mode_and_var = None;
			let mut param = None;
			let loc_of_last_token_in_ty: (usize, usize) = if self.next_in(&[AT]).is_some() {
				self.expect(&[LT], &ErrorHandler::UntilBalanced, Some("'<'"))?;
				if let Some(mode_token_loc) = self.next_in(&[SEPARATED, ERASED]) {
					self.expect(&[APOSTROPHE], &ErrorHandler::UntilBalanced, Some("a \"'\" before a type variable"))?;
					let type_var_token_loc = self.expect(&[IDENT("")], &ErrorHandler::UntilBalanced, Some("a type variable for thie generic struct"))?;
					let type_var_loc = self.id_token_loc_to_loc(&type_var_token_loc);
					let mode_loc = Loc {
						elt: match mode_token_loc.token {
							SEPARATED => PolymorphMode::Separated,
							ERASED => PolymorphMode::Erased,
							_ => unreachable!()
						},
						byte_offset: mode_token_loc.byte_offset, byte_len: mode_token_loc.byte_len, file_id: self.file_id
					};
					mode_and_var = Some((mode_loc, type_var_loc));
				} else {
					let type_param_loc = self.parse_ty(&ErrorHandler::UntilBalanced)?;
					param = Some(type_param_loc);
				}
				let gt_loc = self.expect(&[GT], &ErrorHandler::UntilBalanced, Some("'>'"))?;
				(gt_loc.byte_offset, gt_loc.byte_len)
			} else {
				(name_loc.byte_offset, name_loc.byte_len)
			};
			if self.next_in(&[LBRACE]).is_some() {
				if let Some(type_param) = param {
					//something like `struct A@<i32> { ... }`, not allowed
					self.errors.push(Error{
						err: "Generic struct declarations must be marked as either 'separated' or 'erased'".to_owned(),
						byte_offset: type_param.byte_offset, approx_len: type_param.byte_len, file_id: self.file_id
					});
					self.handle_error(&ErrorHandler::ConsumeIncluding(RBRACE));
					return None;
				}
				//already seen `struct A@<separated 'T>{`
				let mut fields: Vec<(Loc<&'arena Ty<'src, 'arena>>, Loc<&'src str>)> = Vec::new();
				let _rbrace_loc = loop {
					if let Some(loc) = self.next_in(&[RBRACE]) {
						break loc
					}
					let field_ty_loc = self.parse_ty(&ErrorHandler::ConsumeIncluding(RBRACE))?;
					let	name_loc = self.expect(&[IDENT("")], &ErrorHandler::ConsumeIncluding(RBRACE), Some("a name for this field"))?;
					let name_loc = self.id_token_loc_to_loc(&name_loc);
					self.expect(&[SEMI], &ErrorHandler::ConsumeIncluding(RBRACE), Some("';'"))?;
					fields.push((field_ty_loc, name_loc));
				};
				let fields = if fields.is_empty() {&[]} else {&*self.arena.alloc_slice_fill_iter(fields.into_iter())};
				let gdecl = match mode_and_var {
					None => Gdecl::GStructDecl{
						name: name_loc,
						fields
					},
					Some((mode, var)) => Gdecl::GGenericStructDecl{
						name: name_loc,
						var,
						mode,
						fields
					}
				};
				return Some(&*self.arena.alloc(gdecl));
			}
			//not a struct declaration, must be a function return type
			if let Some((mode_loc, var_loc)) = mode_and_var {
				let mode_str = match mode_loc.elt {
					PolymorphMode::Separated => "separated",
					PolymorphMode::Erased => "erased"
				};
				self.errors.push(Error{
					err: format!("Expected a type here, not \"{} '{}\"", mode_str, var_loc.elt),
					byte_offset: mode_loc.byte_offset,
					approx_len: var_loc.byte_offset - mode_loc.byte_offset + var_loc.byte_len,
					file_id: self.file_id
				});
				self.handle_error(&ErrorHandler::UntilBalanced);
				return None;
			}
			let base_return_type = if let Some(type_param) = param {
				Ty::GenericStruct{
					type_param: type_param.getref(self.typecache),
					name: name_loc.elt
				}
			} else {
				Ty::Struct(name_loc.elt)
			};
			let mut base_ty = base_return_type.getref(self.typecache);
			let (mut last_offset, mut last_len) = loc_of_last_token_in_ty;
			loop {
				match self.next_in(&[STAR, LBRACKET]) {
					None => break Loc{
						elt: Some(base_ty),
						byte_offset: struct_loc.byte_offset,
						byte_len: last_offset - struct_loc.byte_offset + last_len,
						file_id: self.file_id
					},
					Some(TokenLoc{token: STAR, byte_offset: star_offset, byte_len: star_len, ..}) => {
						base_ty = Ty::Ptr(Some(base_ty)).getref(self.typecache);
						last_offset = star_offset;
						last_len = star_len;
					},
					Some(TokenLoc{token: LBRACKET, ..}) => {
						let array_len_tok = self.expect(&[INT{val: 0, bits: IntSize::Size8, signed: true}], &ErrorHandler::UntilBalanced, Some("an array length"))?;
						let array_len = match array_len_tok.token {
							INT{val, ..} => val,
							_ => unreachable!()
						};
						let rbracket_loc = self.expect(&[RBRACKET], &ErrorHandler::UntilBalanced, Some("']'"))?;
						last_offset = rbracket_loc.byte_offset;
						last_len = rbracket_loc.byte_len;
						base_ty = Ty::Array{typ: base_ty, length: array_len}.getref(self.typecache);
					},
					Some(_) => unreachable!()
				}
			}
		} else {
			self.parse_ty_or_void(&ErrorHandler::UntilBalanced)?
		};
		//this gdecl is either a function or a global var, either way it will start with a type (or void)
		let name_token_loc = self.expect(&[IDENT("")], &ErrorHandler::UntilBalanced, Some("an identifier"))?;
		let name_loc = self.id_token_loc_to_loc(&name_token_loc);
		if self.next_in(&[SEMI]).is_some() {
			//make sure type is not void
			if let Loc{elt: Some(ty), byte_offset, byte_len, ..} = first_type_loc {
				return Some(&*self.arena.alloc(Gdecl::GVarDecl(
					Loc{
						elt: ty, byte_offset, byte_len, file_id: self.file_id
					},
					name_loc
				)));
			} else {
				//cannot declare a global variable of type void
				self.errors.push(Error{
					err: "Global variables cannot have type void".to_owned(),
					byte_offset: first_type_loc.byte_offset,
					approx_len: first_type_loc.byte_len,
					file_id: self.file_id
				});
				return None;
			}
		}
		//no semicolon, it must be a function declaration
		let mut mode_and_var = None;
		if self.next_in(&[AT]).is_some() {
			self.expect(&[LT], &ErrorHandler::ConsumeIncluding(RBRACE), Some("'<'"))?;
			let mode_token_loc = self.expect(&[SEPARATED, ERASED], &ErrorHandler::ConsumeIncluding(RBRACE), Some("'separated' or 'erased'"))?;
			self.expect(&[APOSTROPHE], &ErrorHandler::ConsumeIncluding(RBRACE), Some("a \"'\" before a type variable"))?;
			let type_var_token_loc = self.expect(&[IDENT("")], &ErrorHandler::ConsumeIncluding(RBRACE), Some("a type variable for this generic function"))?;
			self.expect(&[GT], &ErrorHandler::ConsumeIncluding(RBRACE), Some("'>'"))?;
			let mode_loc = Loc{
				elt: match mode_token_loc.token {
					SEPARATED => PolymorphMode::Separated,
					ERASED => PolymorphMode::Erased,
					_ => unreachable!()
				},
				byte_offset: mode_token_loc.byte_offset,
				byte_len: mode_token_loc.byte_len,
				file_id: self.file_id
			};
			let var_loc = self.id_token_loc_to_loc(&type_var_token_loc);
			mode_and_var = Some((mode_loc, var_loc));
		}
		self.expect(&[LPAREN], &ErrorHandler::UntilBalanced, Some("'('"))?;
		let mut args = Vec::new();
		let _rparen_loc = match self.next_in(&[RPAREN]) {
			Some(l) => l,
			None => loop {
				let arg_ty_loc = self.parse_ty(&ErrorHandler::UntilBalanced)?;
				let name_token_loc = self.expect(&[IDENT("")], &ErrorHandler::UntilBalanced, Some("a name for this function parameter"))?;
				let name_loc = self.id_token_loc_to_loc(&name_token_loc);
				args.push((arg_ty_loc, name_loc));
				if self.next_in(&[COMMA]).is_none() {
					break self.expect(&[RPAREN], &ErrorHandler::UntilBalanced, Some("')'"))?
				}
			}
		};
		let args = if args.is_empty() {&[]} else {&*self.arena.alloc_slice_fill_iter(args.into_iter())};
		let body = self.parse_block(&ErrorHandler::UntilBalanced)?;
		let result = if let Some((mode, var)) = mode_and_var {
			Gdecl::GGenericFuncDecl{
				name: name_loc,
				ret_type: first_type_loc,
				args,
				body: body.elt,
				var,
				mode
			}
		} else {
			Gdecl::GFuncDecl{
				name: name_loc,
				ret_type: first_type_loc,
				args,
				body: body.elt
			}
		};
		Some(&*self.arena.alloc(result))
	}
	pub fn parse_gdecls(mut self) -> (Vec<&'arena Gdecl<'src, 'arena>>, Vec<Error>) {
		let mut gdecls = Vec::new();
		while self.peeker.peek(0).is_some() {
			if let Some(gdecl) = self.parse_gdecl() {
				gdecls.push(gdecl);
			}
		}
		(gdecls, self.errors)
	}
}
