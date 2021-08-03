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
#[allow(clippy::needless_collect)]
fn get_parser<'src, 'arena>(s: &'src str, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>) -> Parser<'src, 'arena, std::vec::IntoIter<TokenLoc<'src>>> {
	let lexer = Lexer::new(s, 0);
	let tokens: Vec<_> = lexer.map(|e| e.unwrap()).flatten().collect();
	Parser::new(tokens.into_iter(), 0, arena, typecache)
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

fn parse_as_block<'src, 'arena>(s: &'src str, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>)
	-> Result<Loc<Block<'src, 'arena>>, Vec<Error>> {
	let mut parser = get_parser(s, arena, typecache);
	match parser.parse_block(&ErrorHandler::Nothing) {
		Some(loc) => Ok(loc),
		None => Err(parser.errors)
	}
}

fn parse_as_gdecl<'src, 'arena>(s: &'src str, arena: &'arena bumpalo::Bump, typecache: &'arena TypeCache<'src, 'arena>)
	-> Result<&'arena Gdecl<'src, 'arena>, Vec<Error>> {
	let mut parser = get_parser(s, arena, typecache);
	match parser.parse_gdecl() {
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

#[test]
fn parse_block_test() {
	let arena = bumpalo::Bump::new();
	let mut typearena = bumpalo::Bump::new();
	let typecache = get_typecache(&mut typearena);
	let test_src =
r##"{
	if null{
		x = f@<i32>(true);
		if false {
		} else if 0 {
			return;
		} else {

		}
	}
	return 0;
	f(3);
	g@<'T>();
	g = 5;
	bool b;
	while null {
		return;
	}
}"##;
	let parsed = parse_as_block(test_src, &arena, &typecache).unwrap();
	use IntSize::*;
	use Stmt::*;
	use Expr::*;
	use Ty::*;
	let expected = 
		Loc { elt: Block( &[
			Loc {
				elt: If( Loc { elt: LitNull, byte_offset: 6, byte_len: 4, file_id: 0, },
					Block( &[
						Loc {
							elt: Assign(
								Loc { elt: Id( "x",), byte_offset: 14, byte_len: 1, file_id: 0, },
								Loc {
									elt: GenericCall {
										name: Loc { elt: "f", byte_offset: 18, byte_len: 1, file_id: 0, },
										type_param: Loc {
											elt: &Int { signed: true, size: Size32, },
											byte_offset: 21, byte_len: 3, file_id: 0,
										},
										args: &[
											Loc { elt: LitBool( true,), byte_offset: 26, byte_len: 4, file_id: 0, },
										],
									}, byte_offset: 18, byte_len: 13, file_id: 0,
								},
							), byte_offset: 14, byte_len: 18, file_id: 0,
						},
						Loc {
							elt: If(
								Loc { elt: LitBool( false,), byte_offset: 38, byte_len: 5, file_id: 0, },
								Block( &[],),
								Block( &[
										Loc {
											elt: If(
												Loc { elt: LitSignedInt( 0, Size64,), byte_offset: 58, byte_len: 1, file_id: 0, },
												Block( &[
														Loc { elt: Return( None,), byte_offset: 65, byte_len: 7, file_id: 0, },
													],
												),
												Block( &[],),
											), byte_offset: 55, byte_len: 33, file_id: 0,
										},
									],
								),
							), byte_offset: 35, byte_len: 53, file_id: 0,
						},
					],),
					Block( &[],),
				), byte_offset: 3, byte_len: 88, file_id: 0,
			},
			Loc {
				elt: Return(
					Some( Loc { elt: LitSignedInt( 0, Size64,), byte_offset: 100, byte_len: 1, file_id: 0, },),
				),
				byte_offset: 93, byte_len: 9, file_id: 0,
			},
			Loc {
				elt: SCall(
					Loc { elt: "f", byte_offset: 104, byte_len: 1, file_id: 0, },
					&[ Loc { elt: LitSignedInt( 3, Size64,), byte_offset: 106, byte_len: 1, file_id: 0, }, ],
				),
				byte_offset: 104, byte_len: 5, file_id: 0,
			},
			Loc {
				elt: GenericSCall {
					name: Loc { elt: "g", byte_offset: 111, byte_len: 1, file_id: 0, },
					type_param: Loc { elt: &TypeVar( "T",), byte_offset: 114, byte_len: 2, file_id: 0, },
					args: &[],
				},
				byte_offset: 111, byte_len: 9, file_id: 0,
			},
			Loc {
				elt: Assign(
					Loc { elt: Id( "g",), byte_offset: 122, byte_len: 1, file_id: 0, },
					Loc { elt: LitSignedInt( 5, Size64,), byte_offset: 126, byte_len: 1, file_id: 0, },
				),
				byte_offset: 122, byte_len: 6, file_id: 0,
			},
			Loc {
				elt: Decl(
					Loc { elt: &Bool, byte_offset: 130, byte_len: 4, file_id: 0, },
					Loc { elt: "b", byte_offset: 135, byte_len: 1, file_id: 0, },
				),
				byte_offset: 130, byte_len: 7, file_id: 0,
			},
			Loc {
				elt: While(
					Loc { elt: LitNull, byte_offset: 145, byte_len: 4, file_id: 0, },
					Block( &[ Loc { elt: Return( None,), byte_offset: 154, byte_len: 7, file_id: 0, }, ],
					),
				),
				byte_offset: 139, byte_len: 25, file_id: 0,
			},
			],
			),
			byte_offset: 0, byte_len: 166, file_id: 0,
		};
	assert_eq!(expected, parsed);
}

#[test]
fn parse_gdecl_tests() {
	let arena = bumpalo::Bump::new();
	let mut typearena = bumpalo::Bump::new();
	let typecache = get_typecache(&mut typearena);
	let tests = vec![
		("bool x;", &Gdecl::GVarDecl(
			Loc{ elt: &Ty::Bool, byte_offset: 0, byte_len: 4, file_id: 0 },
			Loc{ elt: "x", byte_offset: 5, byte_len: 1, file_id: 0 }
		)),
		("extern void f(bool);", &Gdecl::Extern{
			ret_type: Loc{ elt: None, byte_offset: 7, byte_len: 4, file_id: 0 },
			name: Loc{elt: "f", byte_offset: 12, byte_len: 1, file_id: 0},
			arg_types: &[Loc{elt: &Ty::Bool, byte_offset: 14, byte_len: 4, file_id: 0}]
		}),
		("void f(bool x){}", &Gdecl::GFuncDecl{
			ret_type: Loc{ elt: None, byte_offset: 0, byte_len: 4, file_id: 0 },
			name: Loc{elt: "f", byte_offset: 5, byte_len: 1, file_id: 0},
			args: &[(Loc{elt: &Ty::Bool, byte_offset: 7, byte_len: 4, file_id: 0}, Loc{elt: "x", byte_offset: 12, byte_len: 1, file_id: 0})],
			body: Block(&[])
		}),
		("'T g@<separated 'T>('T* x, void* y){return;}", &Gdecl::GGenericFuncDecl{
			ret_type: Loc{elt: Some(&Ty::TypeVar("T")), byte_offset: 0, byte_len: 2, file_id: 0},
			name: Loc{elt: "g", byte_offset: 3, byte_len: 1, file_id: 0},
			args: &[
				(
					Loc{elt: &Ty::Ptr(Some(&Ty::TypeVar("T"))), byte_offset: 20, byte_len: 3, file_id: 0},
					Loc{elt: "x", byte_offset: 24, byte_len: 1, file_id: 0}
				),
				(
					Loc{elt: &Ty::Ptr(None), byte_offset: 27, byte_len: 5, file_id: 0},
					Loc{elt: "y", byte_offset: 33, byte_len: 1, file_id: 0}
				)
			],
			body: Block(&[Loc{ elt: Stmt::Return(None), byte_offset: 36, byte_len: 7, file_id: 0 }]),
			mode: Loc{elt: PolymorphMode::Separated, byte_offset: 6, byte_len: 9, file_id: 0},
			var: Loc{elt: "T", byte_offset: 17, byte_len: 1, file_id: 0}
		}),
		("struct A{}", &Gdecl::GStructDecl{
			name: Loc{elt: "A", byte_offset: 7, byte_len: 1, file_id: 0},
			fields: &[]
		}),
		("struct B@<erased 'T>{'B x; void* y; struct A z;}", &Gdecl::GGenericStructDecl{
			name: Loc{elt: "B", byte_offset: 7, byte_len: 1, file_id: 0},
			var: Loc{elt: "T", byte_offset: 18, byte_len: 1, file_id: 0},
			mode: Loc{elt: PolymorphMode::Erased, byte_offset: 10, byte_len: 6, file_id: 0},
			fields: &[
				(
					Loc{elt: &Ty::TypeVar("B"), byte_offset: 21, byte_len: 2, file_id: 0},
					Loc{elt: "x", byte_offset: 24, byte_len: 1, file_id: 0}
				),
				(
					Loc{elt: &Ty::Ptr(None), byte_offset: 27, byte_len: 5, file_id: 0},
					Loc{elt: "y", byte_offset: 33, byte_len: 1, file_id: 0}
				),
				(
					Loc{elt: &Ty::Struct("A"), byte_offset: 36, byte_len: 8, file_id: 0},
					Loc{elt: "z", byte_offset: 45, byte_len: 1, file_id: 0}
				)
			]
		})
	];
	for (test_str, expected_parse) in tests {
		assert_eq!(expected_parse, parse_as_gdecl(test_str, &arena, &typecache).unwrap());
	}
}
