
fn main() {
	use std::env::var_os;
	//if targeting unix and x86_64, then lld should work
	if var_os("CARGO_CFG_TARGET_FAMILY").as_deref() == Some("unix".as_ref())
		&& var_os("CARGO_CFG_TARGET_ARCH").as_deref() == Some("x86_64".as_ref()) {
		println!("cargo:rustc-env=RUSTFLAGS=-C link-arg=-fuse-ld=lld");
	}

	println!("cargo:rerun-if-changed=build.rs");
}
