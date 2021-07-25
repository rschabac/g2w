#![allow(dead_code)]
use crate::ast;
use crate::driver::Error;

use std::borrow::Cow;
use std::str::Chars;

#[cfg(test)]
mod tests;

const LEX_MAX_PEEK: usize = 2;

struct Peeker<'src> {
	chars: Chars<'src>,
	buf: [char; LEX_MAX_PEEK],
	next_read: u8,
	amount_buffered: u8
}
impl<'src> Peeker<'src> {
	fn new(chars: Chars<'src>) -> Self {
		Peeker{
			chars,
			buf: Default::default(),
			next_read: 0,
			amount_buffered: 0
		}
	}
	//amount is 0-indexed: peek(0) gets the very next char
	fn peek(&mut self, amount: u8) -> Option<char> {
		debug_assert!((amount as usize) < LEX_MAX_PEEK, "Cannot peek ahead {}, need to increase LEX_MAX_PEEK (currently {})", amount, LEX_MAX_PEEK);
		if amount < self.amount_buffered {
			return Some(self.buf[(self.next_read + amount) as usize % LEX_MAX_PEEK]);
		}
		//the requested char is not buffered
		let mut insert_index: u8 = (self.next_read + self.amount_buffered) % LEX_MAX_PEEK as u8;
		for i in 0..(amount - self.amount_buffered + 1) {
			let next_char = match self.chars.next() {
				Some(c) => c,
				None => {
					self.amount_buffered += i;
					return None
				}
			};
			self.buf[insert_index as usize] = next_char;
			insert_index = (insert_index + 1) % LEX_MAX_PEEK as u8;
		}
		self.amount_buffered = amount + 1;
		Some(self.buf[(self.next_read + amount) as usize % LEX_MAX_PEEK])
	}
}

impl<'src> Iterator for Peeker<'src> {
	type Item = char;
	fn next(&mut self) -> Option<char> {
		if self.amount_buffered == 0 {
			//nothing in buf, defer to chars
			self.chars.next()
		} else {
			let result = self.buf[self.next_read as usize];
			self.next_read = (self.next_read + 1) % LEX_MAX_PEEK as u8;
			self.amount_buffered -= 1;
			Some(result)
		}
	}
}


#[derive(Clone, PartialEq, Debug)]
pub enum Token<'src> {
	LPAREN, RPAREN,
	LBRACKET, RBRACKET,
	LBRACE, RBRACE,
	COMMA,
	DOT,
	APOSTROPHE,
	IDENT(&'src str),
	//types
	BOOL,
	INTTYPE{bits: ast::IntSize, signed: bool},
	F32, F64, VOID, STAR,
	STRUCT, AT, SEPARATED, ERASED,
	//literals
	INT{val: i64, bits: ast::IntSize},
	UINT{val: u64, bits: ast::IntSize},
	FLOAT{val: f64, bits: ast::FloatSize},
	NULL, TRUE, FALSE,
	STR(Cow<'src, str>),
	//Comparisons
	LT, LTE, GT, GTE, EQEQ, NOTEQ,
	//Operators
	OR, OROR, AND, ANDAND, XOR,
	SHL, /* << */ SHR, /* >> */ SAR, /* >>> */
	PLUS, MINUS, SLASH, PERCENT,
	TILDE, NOT,
	SIZEOF,
	CAST,
	//statements
	EQ, SEMI, IF, ELSE, WHILE, RETURN,
	EXTERN
}
impl<'src> Default for Token<'src> {
	fn default() -> Self {
		//this string will never be a valid identifier
		Token::IDENT("!@#$%__DEFAULT_TOKEN")
	}
}

#[derive(PartialEq, Clone, Debug)]
pub struct TokenLoc<'src> {
	pub token: Token<'src>,
	pub byte_offset: usize,
	//Tokens need to store their length because of string literals:
	//"a" and "\x61" are represented the same way, but have different byte lens
	pub byte_len: usize
}
impl<'src> Default for TokenLoc<'src> {
	fn default() -> Self {
		TokenLoc{
			token: Default::default(),
			byte_offset: usize::MAX,
			byte_len: usize::MAX,
		}
	}
}

pub struct Lexer<'src> {
	src: &'src str,
	peeker: Peeker<'src>,
	current_byte_offset: usize,
	brace_count: u32,
	file_id: u16
}

//determines if a char is something that can be in an identifier
fn valid_in_ident(c: char) -> bool {
	!c.is_whitespace() && !c.is_ascii_punctuation() && !c.is_control()
}

impl<'src> Lexer<'src> {
	pub fn new(source: &'src str, file_id: u16) -> Self{
		Lexer {
			src: source,
			peeker: Peeker::new(source.chars()),
			current_byte_offset: 0,
			brace_count: 0,
			file_id
		}
	}
	//use these instead of accessing self.peeker directly to automatically increment current_byte_offset
	//whenever chars are removed from the peeker
	fn poll(&mut self) -> Option<char> {
		if let Some(c) = self.peeker.next() {
			self.current_byte_offset += c.len_utf8();
			Some(c)
		} else {
			None
		}
	}
	//if the next char equals the given char, consume it and return true. Ootherwise, return false.
	fn next_is(&mut self, c: char) -> bool {
		if self.peeker.peek(0) == Some(c) {
			self.peeker.next();
			self.current_byte_offset += c.len_utf8();
			true
		} else {
			false
		}
	}
	//advances the peeker, executing `body` on each char until a char is seen that does not satisfy the predicate
	//the first char that does not satisfy the predicate is not consumed.
	fn do_while<Cond: FnMut(char) -> bool, Body: FnMut(char)>(&mut self, mut cond: Cond, mut body: Body) {
		loop {
			match self.peeker.peek(0) {
				None => break,
				Some(c) => {
					if !cond(c) {break}
					self.poll();
					body(c)
				}
			};
		}
	}
	//advances the peeker forward until it has seen the given number of closing braces
	fn advance_until_balanced(&mut self) {
		while self.brace_count > 0 {
			if self.poll() == Some('}') {
				self.brace_count -= 1;
			}
		}
	}
	//If an Error is returned, self is still advanced until brace_count == 0
	pub fn lex_until_balanced_brackets(&mut self) -> Result<Vec<TokenLoc<'src>>, Error> {
		use Token::*;
		let mut result: Vec<TokenLoc<'src>> = Vec::new();
		let mut initial_offset: usize;
		let mut emit = |t, byte_len, initial_offset| result.push(TokenLoc{token: t, byte_offset: initial_offset, byte_len});
		while let Some(c) = self.peeker.next() {
			initial_offset = self.current_byte_offset;
			self.current_byte_offset += c.len_utf8();
			match c {
				//Simple one-char tokens
				'(' => emit(LPAREN, 1, initial_offset),
				')' => emit(RPAREN, 1, initial_offset),
				'[' => emit(LBRACKET, 1, initial_offset),
				']' => emit(RBRACKET, 1, initial_offset),
				'{' => {
					self.brace_count += 1;
					emit(LBRACE, 1, initial_offset);
				},
				'}' => {
					self.brace_count -= 1;
					emit(RBRACE, 1, initial_offset);
					if self.brace_count == 0 {
						break
					}
				},
				',' => emit(COMMA, 1, initial_offset),
				'.' => emit(DOT, 1, initial_offset),
				'@' => emit(AT, 1, initial_offset),
				'+' => emit(PLUS, 1, initial_offset),
				'-' => emit(MINUS, 1, initial_offset),
				'*' => emit(STAR, 1, initial_offset),
				'%' => emit(PERCENT, 1, initial_offset),
				'~' => emit(TILDE, 1, initial_offset),
				';' => emit(SEMI, 1, initial_offset),
				'^' => emit(XOR, 1, initial_offset),
				'\'' => emit(APOSTROPHE, 1, initial_offset),
				//more than one char operands
				'<' => if self.next_is('=') {
						emit(LTE, 2, initial_offset)
					} else if self.next_is('<') {
						emit(SHL, 2, initial_offset)
					} else {
						emit(LT, 1, initial_offset)
					},
				'>' => if self.next_is('=') {
						emit(GTE, 2, initial_offset)	
					} else if self.next_is('>') {
						if self.next_is('>') {
							emit(SAR, 3, initial_offset)
						} else {
							emit(SHR, 2, initial_offset)
						}
					} else {
						emit(GT, 1, initial_offset)
					},
				'=' => if self.next_is('=') {
						emit(EQEQ, 2, initial_offset)
					} else {
						emit(EQ, 1, initial_offset)
					},
				'!' => if self.next_is('=') {
						emit(NOTEQ, 2, initial_offset)
					} else {
						emit(NOT, 1, initial_offset)
					},
				'|' => if self.next_is('|') {
						emit(OROR, 2, initial_offset)
					} else {
						emit(OR, 1, initial_offset)
					},
				'&' => if self.next_is('&') {
						emit(ANDAND, 2, initial_offset)
					} else {
						emit(AND, 1, initial_offset)
					},
				'/' => if self.next_is('/') {
						//line comment, skip until end of line
						//do_while will increment self.current_byte_offset
						//if there is no newline before EOF, do nothing
						self.do_while(|c| c != '\n', |_| {});
					} else if self.next_is('*') {
						//block comment, skip until */ is found
						//if no */ is found, it is an error
						let mut approx_len = '/'.len_utf8() + '*'.len_utf8();
						loop {
							self.do_while(|c| c != '*', |c| {approx_len += c.len_utf8()});
							if self.poll() == None {
								//Either hit EOF right after *, or hit EOF before finding a *
								//in either case, return an error
								self.advance_until_balanced();
								return Err(Error{
									err: "Input file ends without terminating block comment".to_owned(),
									byte_offset: initial_offset,
									approx_len,
									file_id: self.file_id
								});
							} else {
								//the char consumed by self.poll() above must be a '*'
								approx_len += '*'.len_utf8();
							}
							if self.next_is('/') {
								break
							}
						}
					} else {
						emit(SLASH, 1, initial_offset);
					},
				//string literals
				'"' => {
					//look through the string, and if it contains no escape sequences, use a slice of the source as the string
					let mut len: usize = 0;
					let mut lexed_entire_string = false;
					loop {
						match self.peeker.peek(0) {
							None => {
								//string literal runs until EOF
								let error = Error {
									err: "Input file ends without terminating string literal".to_owned(),
									byte_offset: initial_offset,
									approx_len: len + '"'.len_utf8(),
									file_id: self.file_id
								};
								self.advance_until_balanced(); //shouldn't really make a difference, it's already at EOF
								return Err(error);
							},
							Some(c) => {
								if c == '"' {
									self.peeker.next();
									//found the ending ", no escape characters, so represent the string as a &'src str
									let str_literal: &'src str = self.src.get((initial_offset+1)..(initial_offset+1+len)).expect("could not get substr for string lit");
									emit(STR(Cow::Borrowed(str_literal)), len + 2 * '"'.len_utf8(), initial_offset);
									lexed_entire_string = true;
									break
								} else if c == '\\' {
									//escape sequence
									break
								} else {
									self.peeker.next();
									len += c.len_utf8();
								}
							}
						}
					}
					if !lexed_entire_string {
						//an escape sequence was encountered, the '\' was not consumed
						//first, copy the chars that were already scanned
						let mut acc: String = self.src.get((initial_offset+1)..(initial_offset+1+len)).expect("could not get substr to copy to String").to_owned();
						loop {
							match self.peeker.peek(0) {
								None => {
									//string literal runs until EOF
									let error = Error {
										err: "Input file ends without terminating string literal".to_owned(),
										byte_offset: initial_offset,
										approx_len: len + '"'.len_utf8(),
										file_id: self.file_id
									};
									self.advance_until_balanced(); //shouldn't really make a difference, it's already at EOF
									return Err(error);
								},
								Some(c) => {
									if c == '"' {
										self.peeker.next();
										//found the ending "
										emit(STR(Cow::Owned(acc)), len + 2 * '"'.len_utf8(), initial_offset);
										break
									} else if c == '\\' {
										self.poll();
										len += '\\'.len_utf8();
										//escape sequence
										match self.poll() {
											None => {
												let error = Error {
													err: "Input file ends without terminating string literal".to_owned(),
													byte_offset: initial_offset,
													approx_len: len + '"'.len_utf8(),
													file_id: self.file_id
												};
												self.advance_until_balanced();
												return Err(error);
											},
											Some('a') => {len += 1; acc.push(0x07_u8.into())}, //Bell
											Some('b') => {len += 1; acc.push(0x08_u8.into())}, //Backspace
											Some('f') => {len += 1; acc.push(0x0C_u8.into())}, //Formfeed Page Break
											Some('n') => {len += 1; acc.push(0x0A_u8.into())}, //Newline
											Some('r') => {len += 1; acc.push(0x0D_u8.into())}, //Carriage Return
											Some('t') => {len += 1; acc.push(0x09_u8.into())}, //Horizontal Tab
											Some('v') => {len += 1; acc.push(0x0B_u8.into())}, //Vertical Tab
											Some('\\')=> {len += 1; acc.push('\\')}, 			//Backslash
											Some('"') => {len += 1; acc.push('"')},				//Double Quote
											Some('x') => {
												len += 1;
												//consume as many hex digits as possible
												let byte_offset_of_slash = initial_offset + len - 1;
												let mut amount_of_digits = 0;
												let mut hex_acc: u64 = 0;
												//if there are no following hex digits, report an error
												self.do_while(|c| c.is_ascii_hexdigit(), |c| {
													amount_of_digits += 1;
													len += 1;
													hex_acc = 16 * hex_acc + c.to_digit(16).unwrap() as u64;
												});
												if amount_of_digits == 0 {
													let error = Error {
														err: "No hexadecimal digits after \\x escape sequence".to_owned(),
														byte_offset: byte_offset_of_slash,
														approx_len: 2, //just \x
														file_id: self.file_id
													};
													self.advance_until_balanced();
													return Err(error);
												}
												use std::convert::TryFrom;
												let byte_result = match u8::try_from(hex_acc) {
													Ok(x) => x,
													Err(_) => {
														let error = Error {
															err: "\\x escape sequence out of range of u8".to_owned(),
															byte_offset: byte_offset_of_slash,
															approx_len: 2 + amount_of_digits, //2 for \ and x, then the amount of digits seen
															file_id: self.file_id
														};
														self.advance_until_balanced();
														return Err(error);
													}
												};
												acc.push(byte_result.into());
											},
											Some('u') | Some('U') => {
												let error = Error {
													err: "\\u and \\U escape sequences are not yet supported".to_owned(),
													byte_offset: initial_offset + len,
													approx_len: 2,
													file_id: self.file_id
												};
												self.advance_until_balanced();
												return Err(error);
											},
											Some(other) => {
												let error = Error {
													err: format!("Unknown escape sequence \\{}", other),
													byte_offset: initial_offset + len,
													approx_len: 2,
													file_id: self.file_id
												};
												self.advance_until_balanced();
												return Err(error);
											}
										}
									} else {
										self.poll();
										len += c.len_utf8();
										acc.push(c);
									}
								}
							}
						}
					}
				},
				//numeric literals
				'0'..='9' => {
					let mut approx_len = 1; //theoretically, should set approx_len to c.len_utf8(), but it is guaranteed to be 1 here
					//accumulates the value of the integer part of the number
					let mut acc: u64 = c as u64 - '0' as u64;
					//check for hex numbers and octal numbers
					let mut is_hex = false;
					if c == '0' {
						match self.peeker.peek(0) {
							None => {
								//just "0", and hit EOF
								emit(INT{val: 0, bits: ast::IntSize::Size64}, 1, initial_offset);
								break
							},
							Some(d) if d.is_ascii_digit() => {
								self.poll();
								//numeric literal starting with 0, octal literals are not supported
								let error = Error{
									err: "Octal numbers are not supported (integer literals starting with 0)".to_owned(),
									byte_offset: initial_offset,
									approx_len: 2,
									file_id: self.file_id
								};
								self.advance_until_balanced();
								return Err(error);
							},
							which_x @ Some('x') | which_x @ Some('X') => {
								self.poll();
								approx_len += 1;
								//hex number
								is_hex = true;
								acc = 0;
								let mut seen_numbers = false;
								self.do_while(|c| c.is_ascii_hexdigit(), |c| {
									seen_numbers = true;
									approx_len += 1;
									acc = 16 * acc + c.to_digit(16).unwrap() as u64;
								});
								if !seen_numbers {
									//there must be numbers after the 0x
									self.advance_until_balanced();
									return Err(Error{
										err: format!("No hexadecimal digits found after 0{}", which_x.unwrap()),
										byte_offset: initial_offset,
										approx_len: 2,
										file_id: self.file_id
									});
								}
							},
							_ => ()
						};
					}
					//consume (0-9) chars, adjusting the running total
					self.do_while(|c| c.is_ascii_digit(), |c| {
						approx_len += 1;
						//TODO: detect overflow here, give error about literal too big
						acc = 10 * acc + c as u64 - '0' as u64;
					});
					if self.next_is('.') {
						approx_len += 1;
						//Float literal
						if is_hex {
							//can't do something like 0x3A.5
							let error = Error {
								err: "Hexadecimal numbers cannot have a fractional part".to_owned(),
								byte_offset: initial_offset,
								approx_len,
								file_id: self.file_id
							};
							self.advance_until_balanced();
							return Err(error);
						}
						let mut acc_string: String = "0.".to_owned();
						self.do_while(|c| c.is_ascii_digit(), |c| {
							approx_len += 1;
							acc_string.push(c)
						});
						let float_val: f64 = acc_string.parse::<f64>().expect("could not parse accumulated string as f64") + acc as f64;
						let size: ast::FloatSize = if self.next_is('f') {
							approx_len += 1;
							match (self.peeker.peek(0), self.peeker.peek(1)) {
								(Some('3'), Some('2')) => {
									self.poll();
									self.poll();
									approx_len += 2;
									ast::FloatSize::FSize32
								},
								(Some('6'), Some('4')) => {
									self.poll();
									self.poll();
									approx_len += 2;
									ast::FloatSize::FSize64
								},
								(first, second) => {
									approx_len += first.map(char::len_utf8).unwrap_or(0) + second.map(char::len_utf8).unwrap_or(0);
									let error = Error {
										err: "Invalid suffix on a float literal (must be either f32 or f64)".to_owned(),
										byte_offset: initial_offset,
										approx_len ,
										file_id: self.file_id
									};
									self.advance_until_balanced();
									return Err(error);
								}
							}
						} else {
							ast::FloatSize::FSize64
						};
						emit(FLOAT{val: float_val, bits: size}, approx_len, initial_offset);
					} else {
						//int literal
						let signed: bool;
						let mut has_suffix = false;
						if self.next_is('i') {
							approx_len += 1;
							signed = true;
							has_suffix = true;
						} else if self.next_is('u') {
							approx_len += 1;
							signed = false;
							has_suffix = true;
						} else {
							signed = true;
						}
						let size: ast::IntSize;
						if has_suffix {
							match (self.peeker.peek(0), self.peeker.peek(1)) {
								(Some('8'), _) => {
									self.poll();
									approx_len += 1;
									size = ast::IntSize::Size8;
								},
								(Some('1'), Some('6')) => {
									self.poll();
									self.poll();
									approx_len += 2;
									size = ast::IntSize::Size16;
								},
								(Some('3'), Some('2')) => {
									self.poll();
									self.poll();
									approx_len += 2;
									size = ast::IntSize::Size32;
								},
								(Some('6'), Some('4')) => {
									self.poll();
									self.poll();
									approx_len += 2;
									size = ast::IntSize::Size64;
								},
								(first, second) => {
									approx_len += first.is_some() as usize + second.is_some() as usize;
									let error = Error {
										err: "Invalid suffix on integer literal (must be i8, i16, i32, or i64)".to_owned(),
										byte_offset: initial_offset,
										approx_len,
										file_id: self.file_id
									};
									self.advance_until_balanced();
									return Err(error);
								}
							};
						} else {
							size = ast::IntSize::Size64;
						}
						if signed {
							emit(INT{val: acc as i64, bits: size}, approx_len, initial_offset);
						} else {
							emit(UINT{val: acc, bits: size}, approx_len, initial_offset);
						}
					}
				},
				_ if c.is_alphabetic() => {
					let mut len = c.len_utf8();
					//find the offset of the first character that is not allowed in an identifier
					self.do_while(valid_in_ident, |c| len += c.len_utf8());
					debug_assert!(self.src.is_char_boundary(initial_offset + len), "end of ident is not code point boundary");
					let ident: &'src str = self.src.get(initial_offset..(initial_offset + len)).expect("could not get substr for ident");
					const KEYWORDS: &[(&str, Token<'static>)] = &[("bool", BOOL), ("f32", F32), ("f64", F64),
						("i8", INTTYPE{bits: ast::IntSize::Size8, signed: true}),
						("i16", INTTYPE{bits: ast::IntSize::Size16, signed: true}),
						("i32", INTTYPE{bits: ast::IntSize::Size32, signed: true}),
						("i64", INTTYPE{bits: ast::IntSize::Size64, signed: true}),
						("u8", INTTYPE{bits: ast::IntSize::Size8, signed: false}),
						("u16", INTTYPE{bits: ast::IntSize::Size16, signed: false}),
						("u32", INTTYPE{bits: ast::IntSize::Size32, signed: false}),
						("u64", INTTYPE{bits: ast::IntSize::Size64, signed: false}),
						("void", VOID), ("struct", STRUCT), ("separated", SEPARATED), ("erased", ERASED), ("null", NULL), ("true", TRUE), ("false", FALSE), ("sizeof", SIZEOF), ("cast", CAST), ("if", IF), ("else", ELSE), ("while", WHILE), ("return", RETURN), ("extern", EXTERN)];
					let mut found_in_keywords = false;
					for (string, tok) in KEYWORDS.iter() {
						if string == &ident {
							found_in_keywords = true;
							emit(tok.clone(), string.as_bytes().len(), initial_offset);
							break
						}
					}
					if !found_in_keywords {
						emit(IDENT(ident), ident.as_bytes().len(), initial_offset);
					}
				}
				//skip whitespace
				_ if c.is_whitespace() => {},
				//identifiers cannot start with _
				'_' => {
					self.advance_until_balanced();
					return Err(Error{
						err: "Identifiers cannot start with _".to_owned(),
						byte_offset: initial_offset,
						approx_len: 1,
						file_id: self.file_id
					});
				}
				//any other characters are an error
				_ => {
					let err = Error {
						err: format!("Invalid character {} ({:?})", c, c),
						byte_offset: initial_offset,
						approx_len: c.len_utf8(),
						file_id: self.file_id
					};
					self.advance_until_balanced();
					return Err(err);
				}
			};
		}
		//after the loop, either hit the end of the string or brace_count is 0
		Ok(result)
	}
}
impl<'src> Iterator for Lexer<'src> {
	type Item = Result<Vec<TokenLoc<'src>>, Error>;
	fn next(&mut self) -> Option<Self::Item> {
		//if the remaining characters are whitespace, return None
		self.do_while(|c| c.is_whitespace(), |_| {});
		if self.peeker.peek(0) == None {
			None
		} else {
			Some(self.lex_until_balanced_brackets())
		}
	}
}
