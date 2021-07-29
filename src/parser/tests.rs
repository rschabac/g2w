use crate::parser::{Parser, ErrorHandler};
use crate::lexer::{Lexer, TokenLoc};
use crate::ast2::*;
use crate::driver::Error;

fn get_typecache<'src, 'arena>(arena: &'arena mut bumpalo::Bump) -> TypeCache<'src, 'arena> {
	TypeCache{
		arena: std::sync::Mutex::new(arena),
		cached: std::sync::RwLock::new(std::collections::HashMap::new())
	}
}
fn get_parser<'src, 'arena>(s: &'src str, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Parser<'src, 'arena, std::vec::IntoIter<TokenLoc<'src>>> {
	let lexer = Lexer::new(s, 0);
	let all_tokens_iter: Vec<_> = lexer.map(|e| e.unwrap()).flatten().collect();
	Parser::new(all_tokens_iter.into_iter(), 0, arena, typecache)
}

fn parse_as_ty<'src, 'arena>(s: &'src str, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>)
	-> Result<Loc<&'arena Ty<'src, 'arena>>, Vec<Error>> {
	let mut parser = get_parser(s, arena, typecache);
	match parser.parse_ty(&ErrorHandler::Nothing) {
		Some(loc) => Ok(loc),
		None => Err(parser.errors)
	}
}

fn parse_as_expr<'src, 'arena>(s: &'src str, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>)
	-> Result<Loc<Expr<'src, 'arena>>, Vec<Error>> {
	let mut parser = get_parser(s, arena, typecache);
	match parser.parse_expr(&ErrorHandler::Nothing) {
		Some(loc) => Ok(loc),
		None => Err(parser.errors)
	}
}

#[test]
fn parse_type_tests() {
	let arena = bumpalo::Bump::new();
	let mut typearena = bumpalo::Bump::new();
	let typecache = get_typecache(&mut typearena);
	let tests = vec![
		("u8", Loc{elt: &Ty::Int{signed: false, size: IntSize::Size8}, byte_offset: 0, byte_len: 2, file_id: 0}),
		("void\n*", Loc{elt: &Ty::Ptr(None), byte_offset: 0, byte_len: 6, file_id: 0}),
		("struct\tvector @ <'T[4]* >  ", Loc{
			elt: &Ty::GenericStruct{
				type_param: &Ty::Ptr(Some(
					&Ty::Array{
						length: 4,
						typ: &Ty::TypeVar("T")
					}
				)),
				name: "vector"
			},
			byte_offset: 0, byte_len: 25, file_id: 0
		})
	];
	for (test_str, expected_parse) in tests {
		assert_eq!(expected_parse, parse_as_ty(test_str, &arena, &typecache).unwrap());
	}
}

#[test]
fn parse_expr_tests() {
	let arena = bumpalo::Bump::new();
	let mut typearena = bumpalo::Bump::new();
	let typecache = get_typecache(&mut typearena);
	let tests = vec![
		("true", Loc{elt: Expr::LitBool(true), byte_offset: 0, byte_len: 4, file_id: 0}),
		("*array[(5)].data", Loc{
			elt: Expr::Deref(Loc{
				elt: &Expr::Proj(Loc{
					elt: &Expr::Index(Loc{
						elt: &Expr::Id("array"),
						byte_offset: 1, byte_len: 5, file_id: 0
					}, Loc{
						elt: &Expr::LitSignedInt(5, IntSize::Size64),
						byte_offset: 7, byte_len: 3, file_id: 0
					}),
					byte_offset: 1, byte_len: 10, file_id: 0
				}, Loc{
					elt: "data",
					byte_offset: 12, byte_len: 4, file_id: 0
				}),
				byte_offset: 1, byte_len: 15, file_id: 0
			}),
			byte_offset: 0, byte_len: 16, file_id: 0
		}),
		("f@<i32>(g( ), sizeof(i32), cast(i8, 0))", Loc {
			elt: Expr::GenericCall {
				name: Loc { elt: "f", byte_offset: 0, byte_len: 1, file_id: 0},
				type_param: Loc {
					elt: &Ty::Int { signed: true, size: IntSize::Size32},
					byte_offset: 3, byte_len: 3, file_id: 0
				},
				args: &[
					Loc {
						elt: Expr::Call(
							Loc { elt: "g", byte_offset: 8, byte_len: 1, file_id: 0},
							&[],
						),
						byte_offset: 8, byte_len: 4, file_id: 0
					},
					Loc {
						elt: Expr::Sizeof(
							Loc {
								elt: &Ty::Int { signed: true, size: IntSize::Size32, },
								byte_offset: 21, byte_len: 3, file_id: 0,
							},
						),
						byte_offset: 14, byte_len: 11, file_id: 0,
					},
					Loc {
						elt: Expr::Cast(
							Loc {
								elt: &Ty::Int { signed: true, size: IntSize::Size8, },
								byte_offset: 32, byte_len: 2, file_id: 0,
							},
							Loc {
								elt: &Expr::LitSignedInt( 0, IntSize::Size64,),
								byte_offset: 36, byte_len: 1, file_id: 0,
							},
						),
						byte_offset: 27, byte_len: 11, file_id: 0,
					},
				],
			},
			byte_offset: 0, byte_len: 39, file_id: 0,
		}),
		("a - b - c == d && e << f % g", Loc {
			elt: Expr::Binop(
				Loc {
					elt: &Expr::Binop(
						Loc {
							elt: &Expr::Binop(
								Loc {
									elt: &Expr::Binop(
										Loc { elt: &Expr::Id( "a",), byte_offset: 0, byte_len: 1, file_id: 0, },
										BinaryOp::Sub,
										Loc { elt: &Expr::Id( "b",), byte_offset: 4, byte_len: 1, file_id: 0, },
									),
									byte_offset: 0, byte_len: 5, file_id: 0,
								},
								BinaryOp::Sub,
								Loc { elt: &Expr::Id( "c",), byte_offset: 8, byte_len: 1, file_id: 0, },
							),
							byte_offset: 0, byte_len: 9, file_id: 0,
						},
						BinaryOp::Equ,
						Loc { elt: &Expr::Id( "d",), byte_offset: 13, byte_len: 1, file_id: 0, },
					),
					byte_offset: 0, byte_len: 14, file_id: 0,
				},
				BinaryOp::And,
				Loc {
					elt: &Expr::Binop(
						Loc { elt: &Expr::Id( "e",), byte_offset: 18, byte_len: 1, file_id: 0, },
						BinaryOp::Shl,
						Loc {
							elt: &Expr::Binop(
								Loc { elt: &Expr::Id( "f",), byte_offset: 23, byte_len: 1, file_id: 0, },
								BinaryOp::Mod,
								Loc { elt: &Expr::Id( "g",), byte_offset: 27, byte_len: 1, file_id: 0, },
							),
							byte_offset: 23, byte_len: 5, file_id: 0,
						},
					),
					byte_offset: 18, byte_len: 10, file_id: 0,
				},
			),
			byte_offset: 0, byte_len: 28, file_id: 0,
		})
	];
	for (test_str, expected_parse) in tests {
		assert_eq!(expected_parse, parse_as_expr(test_str, &arena, &typecache).unwrap());
	}
}