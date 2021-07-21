use crate::lexer::*;

fn lex_str(s: &'static str) -> Vec<TokenLoc<'static>> {
	let mut lexer = Lexer::new(s);
	lexer.lex_until_balanced_brackets().unwrap()
}

#[test]
fn simple_tokens() {
	use Token::*;
	let vec_of_token_locs = lex_str("(  )[], .@\t\n+\r-*/%~;^'");
	let expected_tokens_and_offsets = &[(LPAREN, 0), (RPAREN, 3), (LBRACKET, 4), (RBRACKET, 5), (COMMA, 6), (DOT, 8), (AT, 9), (PLUS,12), (MINUS, 14), (STAR, 15), (SLASH, 16), (PERCENT, 17), (TILDE, 18), (SEMI, 19), (XOR, 20), (APOSTROPHE, 21)];
	assert_eq!(expected_tokens_and_offsets.len(), vec_of_token_locs.len());
	for (given_token_loc, (expected_token, expected_offset)) in vec_of_token_locs.iter().zip(expected_tokens_and_offsets) {
		let expected_token_loc = TokenLoc{
			token: expected_token.clone(),
			byte_offset: *expected_offset,
			byte_len: 1
		};
		assert_eq!(&expected_token_loc, given_token_loc);
	}
}

#[test]
fn complex_operands() {
	use Token::*;
	let vec_of_token_locs = lex_str("<<=>>>>>|>=!====&&&|||");
	let expected_token_locs = &[(SHL, 0, 2), (EQ, 2, 1), (SAR, 3, 3), (SHR, 6, 2), (OR, 8, 1), (GTE, 9, 2), (NOTEQ, 11, 2), (EQEQ, 13, 2), (EQ, 15, 1), (ANDAND, 16, 2), (AND, 18, 1), (OROR, 19, 2), (OR, 21, 1)];
	assert_eq!(expected_token_locs.len(), vec_of_token_locs.len());
	for (given_token_loc, expected) in vec_of_token_locs.iter().zip(expected_token_locs) {
		let expected_token_loc = TokenLoc{
			token: expected.0.clone(),
			byte_offset: expected.1,
			byte_len: expected.2
		};
		assert_eq!(&expected_token_loc, given_token_loc);
	}
}

#[test]
fn string_literal() {
	use Token::*;
	use std::borrow::Cow;
	let vec_of_token_locs = lex_str(r#" "abcde" "#);
	assert_eq!(1, vec_of_token_locs.len());
	assert_eq!(TokenLoc{
		token: STR(Cow::Borrowed("abcde")),
		byte_offset: 1,
		byte_len: 7
	}, vec_of_token_locs[0]);
}

#[test]
fn string_literal_with_simple_escapes() {
	use Token::*;
	use std::borrow::Cow;
	let vec_of_token_locs = lex_str(r#" "hello\a\b\f\n\r\t\v\\\"world" "#);
	assert_eq!(1, vec_of_token_locs.len());
	assert_eq!(TokenLoc{
		token: STR(Cow::Owned("hello\x07\x08\x0C\n\r\t\x0B\\\"world".to_owned())),
		byte_offset: 1,
		byte_len: 30
	}, vec_of_token_locs[0]);
}

#[test]
fn string_literal_with_hex_escapes() {
	use Token::*;
	use std::borrow::Cow;
	let token_locs = lex_str(r#" "hello\xA\xa\x00a\x00" "#);
	assert_eq!(1, token_locs.len());
	assert_eq!(TokenLoc{
		token: STR(Cow::Owned("hello\n\n\n\0".to_owned())),
		byte_offset: 1,
		byte_len: 22
	}, token_locs[0]);
}

#[test]
fn numeric_literals() {
	use Token::*;
	use crate::ast::IntSize::*;
	use crate::ast::FloatSize::*;
	let source = "123 123u32 123.0 123. 123.5f32 0 0.f64 0xA 0X123aBcu64";
	let token_locs = lex_str(source);
	assert_eq!(9, token_locs.len());
	let expected = &[
		TokenLoc{token: INT{val: 123, bits: Size64}, byte_offset: 0, byte_len: 3},
		TokenLoc{token: UINT{val: 123, bits: Size32}, byte_offset: 4, byte_len: 6},
		TokenLoc{token: FLOAT{val: 123.0, bits: FSize64}, byte_offset: 11, byte_len: 5},
		TokenLoc{token: FLOAT{val: 123.0, bits: FSize64}, byte_offset: 17, byte_len: 4},
		TokenLoc{token: FLOAT{val: 123.5, bits: FSize32}, byte_offset: 22, byte_len: 8},
		TokenLoc{token: INT{val: 0, bits: Size64}, byte_offset: 31, byte_len: 1},
		TokenLoc{token: FLOAT{val: 0.0, bits: FSize64}, byte_offset: 33, byte_len: 5},
		TokenLoc{token: INT{val: 0xA, bits: Size64}, byte_offset: 39, byte_len: 3},
		TokenLoc{token: UINT{val: 0x123abc, bits: Size64}, byte_offset: 43, byte_len: 11}
	];
	for (expected, given) in expected.iter().zip(token_locs.iter()) {
		assert_eq!(expected, given);
	}
}

#[test]
fn keywords() {
	use Token::*;
	let token_locs = lex_str("bool f32 f64 i8\nu16,void.struct separated extern");
	assert_eq!(11, token_locs.len());
	let expected = &[
		TokenLoc{token: BOOL, byte_offset: 0, byte_len: 4},
		TokenLoc{token: F32, byte_offset: 5, byte_len: 3},
		TokenLoc{token: F64, byte_offset: 9, byte_len: 3},
		TokenLoc{token: INTTYPE{bits: crate::ast::IntSize::Size8, signed: true}, byte_offset: 13, byte_len: 2},
		TokenLoc{token: INTTYPE{bits: crate::ast::IntSize::Size16, signed: false}, byte_offset: 16, byte_len: 3},
		TokenLoc{token: COMMA, byte_offset: 19, byte_len: 1},
		TokenLoc{token: VOID, byte_offset: 20, byte_len: 4},
		TokenLoc{token: DOT, byte_offset: 24, byte_len: 1},
		TokenLoc{token: STRUCT, byte_offset: 25, byte_len: 6},
		TokenLoc{token: SEPARATED, byte_offset: 32, byte_len: 9},
		TokenLoc{token: EXTERN, byte_offset: 42, byte_len: 6},
	];
	for (expected, given) in expected.iter().zip(token_locs.iter()) {
		assert_eq!(expected, given);
	}
}

#[test]
fn idents() {
	use Token::*;
	const LEVITATING_EMOJI: &str = "\u{1F574}";
	let token_locs = lex_str("abc(x\u{1F574}+y\u{1F574}z");
	assert_eq!(5, token_locs.len());
	let expected = &[
		TokenLoc{token: IDENT("abc"), byte_offset: 0, byte_len: 3},
		TokenLoc{token: LPAREN, byte_offset: 3, byte_len: 1},
		TokenLoc{token: IDENT("x\u{1F574}"), byte_offset: 4, byte_len: 1 + '\u{1F574}'.len_utf8()},
		TokenLoc{token: PLUS, byte_offset: 4 + 1 + '\u{1F574}'.len_utf8(), byte_len: 1},
		TokenLoc{token: IDENT("y\u{1F574}z"), byte_offset: 6 + '\u{1F574}'.len_utf8(), byte_len: 2 + '\u{1F574}'.len_utf8()},
	];
	for (expected, given) in expected.iter().zip(token_locs.iter()) {
		assert_eq!(expected, given);
	}
}

#[test]
fn line_comments() {
	use Token::*;
	let token_locs = lex_str("+//abc\"*/whatever&_\n=");
	assert_eq!(2, token_locs.len());
	let expected = &[
		TokenLoc{token: PLUS, byte_offset: 0, byte_len: 1},
		TokenLoc{token: EQ, byte_offset: 20, byte_len: 1}
	];
	for (expected, given) in expected.iter().zip(token_locs.iter()) {
		assert_eq!(expected, given);
	}
}

#[test]
fn block_comments() {
	use Token::*;
	let token_locs = lex_str(r#"*/*_*$"*/^"#);
	assert_eq!(2, token_locs.len());
	let expected = &[
		TokenLoc{token: STAR, byte_offset: 0, byte_len: 1},
		TokenLoc{token: XOR, byte_offset: 9, byte_len: 1}
	];
	for (expected, given) in expected.iter().zip(token_locs.iter()) {
		assert_eq!(expected, given);
	}
}

#[test]
fn lexing_in_chunks() {
	use Token::*;
	let source = r#"bool void{erased if{f32}}return{.}"#;
	let mut lexer = Lexer::new(source);
	let chunk1 = lexer.lex_until_balanced_brackets().unwrap();
	assert_eq!(9, chunk1.len());
	let expected_chunk1 = &[
		TokenLoc{token: BOOL, byte_offset: 0, byte_len: 4},
		TokenLoc{token: VOID, byte_offset: 5, byte_len: 4},
		TokenLoc{token: LBRACE, byte_offset: 9, byte_len: 1},
		TokenLoc{token: ERASED, byte_offset: 10, byte_len: 6},
		TokenLoc{token: IF, byte_offset: 17, byte_len: 2},
		TokenLoc{token: LBRACE, byte_offset: 19, byte_len: 1},
		TokenLoc{token: F32, byte_offset: 20, byte_len: 3},
		TokenLoc{token: RBRACE, byte_offset: 23, byte_len: 1},
		TokenLoc{token: RBRACE, byte_offset: 24, byte_len: 1},
	];
	for (expected, given) in expected_chunk1.iter().zip(chunk1.iter()) {
		assert_eq!(expected, given);
	}

	let chunk2 = lexer.lex_until_balanced_brackets().unwrap();
	assert_eq!(4, chunk2.len());
	let expected_chunk2 = &[
		TokenLoc{token: RETURN, byte_offset: 25, byte_len: 6},
		TokenLoc{token: LBRACE, byte_offset: 31, byte_len: 1},
		TokenLoc{token: DOT, byte_offset: 32, byte_len: 1},
		TokenLoc{token: RBRACE, byte_offset: 33, byte_len: 1},
	];
	for (expected, given) in expected_chunk2.iter().zip(chunk2.iter()) {
		assert_eq!(expected, given);
	}

	let chunk3 = lexer.lex_until_balanced_brackets().unwrap();
	assert!(chunk3.is_empty());
}

//testing lex errors
//not testing the error messages, those might change, just the byte_offset and approx_len
fn lex_str_err(s: &'static str) -> LexError {
	let mut lexer = Lexer::new(s);
	lexer.lex_until_balanced_brackets().unwrap_err()
}

#[test]
fn unterminated_string() {
	//unterminated string without escape sequences
	let err = lex_str_err(r#" .("abc"#);
	assert_eq!(3, err.byte_offset);
	assert_eq!(4, err.approx_len);
	
	//unterminated string with escape sequences
	let err = lex_str_err(r#"."a\n\xA"#);
	assert_eq!(1, err.byte_offset);
	assert_eq!(7, err.approx_len);
}

#[test]
fn unterminated_block_comment() {
	let err = lex_str_err("/*/");
	assert_eq!(0, err.byte_offset);
	assert_eq!(3, err.approx_len);
}

#[test]
fn bad_escape_sequence() {
	//no hex digits after \x
	let err = lex_str_err(r#""ab\x""#);
	assert_eq!(3, err.byte_offset);
	assert_eq!(2, err.approx_len);

	//number specified in \x too big for u8
	let err = lex_str_err(r#""ab\x100""#);
	assert_eq!(3, err.byte_offset);
	assert_eq!(5, err.approx_len);

	//\z is not an escape sequence
	let err = lex_str_err(r#""ab\z""#);
	assert_eq!(3, err.byte_offset);
	assert_eq!(2, err.approx_len);
}

#[test]
fn bad_numeric_literal() {
	//no hex digits after 0x
	let err = lex_str_err("0x");
	assert_eq!(0, err.byte_offset);
	assert_eq!(2, err.approx_len);

	//hex numbers cannot have a float part
	let err = lex_str_err("0x3a.5e");
	assert_eq!(0, err.byte_offset);
	assert_eq!(5, err.approx_len);

	//invalid size suffix on float
	let err = lex_str_err("3.14f48");
	assert_eq!(0, err.byte_offset);
	assert_eq!(7, err.approx_len);

	//invalid size suffix on integer
	let err = lex_str_err("3i128");
	assert_eq!(0, err.byte_offset);
	assert_eq!(4, err.approx_len);
}

#[test]
fn wayward_underscore() {
	let err = lex_str_err("u8* _x");
	assert_eq!(4, err.byte_offset);
	assert_eq!(1, err.approx_len);
}

#[test]
fn invalid_character() {
	let err = lex_str_err("u8* x$");
	assert_eq!(5, err.byte_offset);
	assert_eq!(1, err.approx_len);
}
