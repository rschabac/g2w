G2W
---
### **G**enerics, **2** **W**ays
A proof of concept of a C-like programming language, with generic data structures and functions implemented
two different ways.

```c-language
//"Separated" mode: Create different copies of this struct
//every time it is used with a different type
struct vec@<separated 'T> {
	'T* data;
	u64 size;
	u64 capacity;
}

//Any time you call vec_new@<some_type>() in your code, a copy of this
//function will be made.
struct vec@<'T> vec_new@<separated 'T>(u64 initial_capacity) {
	...
}

//"Erased" mode: the size of this struct is computed at runtime because
//it depends on the size of the type parameter 'T
struct A@<erased 'T> {
	'T t1;
	i32 x;
	...
}

//This function will only be compiled once, but can work with any type parameter
//Has the same semantics as if it were marked separated
struct A@<'T> new@<erased 'T>(i32 x){
	struct A@<'T> result;
	result.x = x;
	return result;
}
```

Because the goal of this language was to proof out the concepts, many convenience features
you may expect from other languages are not implemented, as they are not necessary to demonstrate the new ideas
that this language introduces. I do not recommend using this language for any large-scale software projects.

See the [Tutorial](tutorial.md) for an explanation of how the language works.

### FAQ

* What features were left out for simplicity?
* What is coming in future versions?

### Requirements
- Clang
If you can\'t run `clang` from the same command line you run this project from, it will not work.
- Unix-like system
I\'ve only tested this on Linux, but MacOS and BSD should be close enough.
All platform-specific work is delegated to clang as much as possible.
You\'re welcome to try this on Windows, but you will either have to run the linker manually, or get clang to detect `link.exe`

### Building

You will need an installation of [Rust](https://www.rust-lang.org/) in order to compile this project.
I recommend the latest stable release of the rust compiler.

To build:

```
git clone https://github.com/rschabac/g2w
cd lang
cargo build --release
```

To run tests:

```
cargo test --all
```
