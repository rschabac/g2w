extern crate lalrpop;

fn main() {
	use std::env::var_os;
	//if targeting unix and x86_64, then lld should work
	if var_os("CARGO_CFG_TARGET_FAMILY").as_deref() == Some("unix".as_ref())
		&& var_os("CARGO_CFG_TARGET_ARCH").as_deref() == Some("x86_64".as_ref()) {
		println!("cargo:rustc-env=RUSTFLAGS=-C link-arg=-fuse-ld=lld");
	}
	//should prevent cargo run from rebuilding the project
	println!("cargo:rerun-if-changed=src/oldparser.lalrpop");
	lalrpop::process_root().unwrap();

	println!("cargo:rerun-if-changed=build.rs");
}
