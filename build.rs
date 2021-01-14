extern crate lalrpop;

fn main() {
	//should prevent cargo run from rebuilding the project
	println!("cargo:rerun-if-changed=src/parser.lalrpop");
	lalrpop::process_root().unwrap();
}
