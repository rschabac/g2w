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
			return Some(std::mem::take(&mut self.buf[(self.next_read + amount) as usize % PARSE_MAX_PEEK]));
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
		Some(std::mem::take(&mut self.buf[(self.next_read + amount) as usize % PARSE_MAX_PEEK]))
	}
}
impl<'src, T: Iterator<Item = TokenLoc<'src>>> Iterator for Peeker<'src, T> {
	type Item = TokenLoc<'src>;
	fn next(&mut self) -> Option<TokenLoc<'src>> {
		if self.amount_buffered == 0 {
			//nothing in buf, defer to base iterator
			self.tokens.next()
		} else {
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
}
impl<'src: 'arena, 'arena, T: Iterator<Item = TokenLoc<'src>>> Parser<'src, 'arena, T> {
	pub fn new(chunk_of_tokens: T, file_id: u16, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Self {
		Parser{
			peeker: Peeker::new(chunk_of_tokens),
			errors: Vec::new(),
			file_id,
			arena,
			typecache
		}
	}
	pub fn parse_gdecls(self) -> (Vec<&'arena Gdecl<'src, 'arena>>, Vec<Error>) {
		//let first_token_byte_offset = self.peeker.next().unwrap().byte_offset;
		let first_token_byte_offset = self.arena as *const _ as usize;
		let ty: &'arena Ty<'src, 'arena> = &*self.arena.alloc(Ty::Bool);
		let ty = ty.getref(self.typecache);
		let ty_loc = Loc{elt: ty, byte_offset: 0, byte_len: 0};
		let name = &*Box::leak(format!("file_{}_{}", self.file_id, first_token_byte_offset).into_boxed_str());
		let name_loc = Loc{elt: name, byte_offset: 0, byte_len: 0};
		let temp = &*self.arena.alloc(Gdecl::GVarDecl(ty_loc, name_loc));
		(vec![temp], self.errors)
	}
}
