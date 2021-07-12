G2W is a systems programming language: it compiles to native code, allows memory to be directly manipulated,
and has no runtime overhead. It is most similar to C.

### Basics

Variables, functions, pointers, and structs work the same way they do in C.

Unlike C, there is a dedicated `bool` type, and constants `true` and `false`.
Integer types have a more regular pattern than they do in C: they start with either `i` for signed or `u` for unsigned,
followed by the number of bits, which must be either 8, 16, 32, or 64. For example, `u64` represents
an unsigned 64-bit integer. There are also the `f32` and `f64` types, which are floating point numbers
with the specified number of bits, equivalent to `float` and `double` in C.

Similar to C, pointer types are denoted using a trailing `*` (e.g. `u8*`). The `void*` type works
the same way it does in C. Arrays of a constant length are represented with the length in brackets
after the type. For example, `i32[7]` is the type of an array of 7 `i32` values.

Structs are similar to C structs, but can only be referred to using the `struct` keyword, followed by their name (there is no `typedef`).

When using generics, a "type variable" can be used to represent a type that the struct/function is parameterized over (more on generics later).
These type variables must start with a `'` character, followed by a name.

Currently, there are no function pointers. Hopefully, this will change in the near future.

Casting uses a different syntax than C. Instead of `(i32) x`, the syntax is `cast(i32, x)`
Compared to most languages, there are much less implicit conversions between types (almost none).
For example, numeric values can only be added together if they have the same signedness and the same size.
Integer literals are always `i64`, or `u64` if suffixed with `u` (I plan on improving this when I rewrite the parser).
`void*` does not automatically convert to/from other pointer types. All of this means that you will have to explicitly cast between
types more often.

There are no `union` types like in C. Types and values cannot be marked as `const` as in C.

### Separated Generics

The first way of using generic structs or functions is the same way they work in C++ or Rust. The compiler will detect all uses
of that struct or function in the code, and create copies of it with its type variable replaced with the type it was used with.

Example: a generic resizable array:
```
struct vec@<separated 'T>{
	'T* data;
	u64 size;
	u64 capacity;
}

struct vec@<'T> create_new_vec@<separated 'T>() {
	...
}

void append_to_vec@<separated 'T>(struct vec@<'T>* v, 'T new_element) {
	...
}
```

Given just the above code, no code will be generated, since the struct and the functions were never used anywhere.
However, if they are used, ...

```
i32 main(){
	struct vec@<f64> x;
	x = create_new_vec@<f64>();
	append_to_vec@<f64>(0.1);

	struct vec@<i8> y;

	return cast(i32, 0);
}
```

... a copy of struct `vec` will be created for `f64` and `i8`, and copies of the functions `create_new_vec` and `append_to_vec`
will be created for `f64`. Since clang sees these as seperate functions, it can generate code that is optimized for each instance.

### Erased Generics

The second way of using generic structs or functions is to generate one version of each, which is provided with just enough information
to handle the generic data it manipulates. Compared to a normal struct, using an erased struct is the same, only that some of the
work that would have been done an compile-time is now being done an runtime. The size of a normal struct is computed at compile-time
based on the size of all of its fields. The offset of any field within this struct is also computed at compile time. In an erased struct,
this calculation cannot be done at compile time because the size of the fields could be different at different times in the program.
Instead, the size of the struct and the offsets of each field are computed when needed, at runtime.

Let\'s say the struct `A` is defined like so:
```
struct A@<erased 'T>{
	i32 x;
	'T y;
	u8 z;
}
```

To declare a variable of type `struct A@<void*>`, the compiler will emit code that computes the size of each field
(in this example, `i32`, `void*`, and `u8`), add them together, and then allocate that much space on the program stack.
(Note: Some adjustment has to be done to account for alignment, more on that later).

How about declaring a variable of type `struct A@<'T>`? Well, since this declaration uses a type variable `'T`, it must be
in a generic function (the typechecker will make sure of that). If it is inside of a separated function, then the type will be
known at compile time (it will be different in each copy of the function that is generated), and the compiler can calculate its size.
If it is inside of an erased function, the size of `'T` could be different at different times. All erased functions are augmented
to take an additional argument that contains the size of the type used for that function call. The compiler automatically
adds this argument to the declaration of the function, and any calls to the function. This hidden parameter will be used when
computing the size of the variable being declared.

Normally, C programmers are very cautious of allocating unknown amounts of memory on the stack. In most cases, it is best to avoid
dynamically adjusting the stack pointer in C via variable-length arrays or the `alloca` function. However, the dynamic stack allocations
caused by erased structs cannot be controlled by external data. The only way to cause a large stack allocation is to use a large struct.
In a sense, the size of an erased struct is some compile-time value, the compiler just does not know *which* value it will be.

Erased structs have the same semantics as separated structs: when passed to a function as an argument, or returned from a function,
the whole struct\'s memory is copied into/out of that function. The only difference is that the amount of memory to copy is computed at runtime.

LLVM\'s type system does not support these kinds of dynamically-sized types, so the resulting code will not be optimized as well
as if the structs/functions had been marked as separated.

###### Note on Alignment

Due to alignment requirements on most types, the size of an erased struct is not simply the sum of the sizes of its fields.
Instead, the size of each field is rounded up to the nearest multiple of 8, and then added together. 8 is the largest required alignment
out of any type that G2W supports, so the field of an erased struct will be correctly aligned no matter what type parameter is used.
This packing algorithm is certainly wasteful: the size of `struct A@<i8>` will be 24 bytes, even though it could be 8 bytes if it
was packed more efficiently (non-generic and separated structs are laid out by LLVM, which will pack them efficiently). Even though
the packing algorithm used by erased structs must run at runtime, it would still be better for performance to compute a better packing.
This will hopefully be implemented soon.

### Interactions between Separated and Erased Structs

Since erased structs can have different type parameters, they cannot pass their type parameter to any separated structs.

```
struct S@<separated 'U>{
	'U x;
	u64* y;
}

struct E@<erased 'T>{
	struct S@<i32> a; //Ok, the type parameter passed to struct S does not depend on 'T
	struct S@<'T> b; //Not ok, code that is using this struct wouldn't know what copy of struct S to use here
	struct S@<'T>* c; //Still not ok, even though it is behind a pointer
	struct S@<struct other_erased_struct@<'T*>[10]> c; //the type being passed to struct S contains a 'T somewhere in it, so this is not valid
}
```

Similarly, a type variable that comes from the signature of an erased function cannot be passed to a separated function or struct.

```
void s@<separated 'T>(){
}

void e@<erased 'T>(){
	s@<i32>(); //Ok, the compiler knows what copy of s to call here
	s@<'T>(); //Not ok, the compiler does not know what copy of s to call here
	struct S@<'T> a; //Not ok, the compiler does not know what copy of struct S to use here
}
```

### Separated vs. Erased

Separated:
✔	Code will be optimized better
❌	Longer compile times
❌	Bigger executable files

Erased:
✔	Faster compilation
✔	Smaller executable files
❌	Cannot be optimized as well
❌	Cannot use separated structs/functions with an erased type variable

### Limitations

Because G2W was intended as a proof of concept, certain convenience features that are not necessary for a working prototype are not included. These include:
* `for` loops
* Increment and operator-assignment (`x++` and `x += 1` will not work)
* Declaring and assigning to a variable in one statement (hopefully coming soon though)
* Generic structs/functions can only have one type parameter, cannot be generic over two or more types
* Generic functions have no information about the type they are passed (other than its size). This means that generic functions cannot do any type-specific operations on generic data, and can only move/copy it around. In the future, function pointers will provide a solution to this.

### Compilation model
Currently, the compiler will read all the `.src` files it is given as input, concatenate them into one big string, and compile that into a single `.ll` file. This will likely change soon. The `.ll` file,
along with all `.c`, `.ll`, `.bc`, `.s`, and `.o` files will be passed to clang to produce an executable (unless command-line options specify otherwise).

To use a function defined in a `.c`, `.ll`, `.bc`, `.s`, or `.o` file, declare the function as `extern` in the `.src` file, with the correct type signature.
```
extern i32 open(u8*, i32);
```

There is no preprocessor like there is in C or C++.

### Interfacing with C
Since G2W has a type system similar to C (without generics), interfacing with C is very simple. Non-generic structs should be laid out
the same way as they are in C (I\'m counting on LLVM for this, but if you want to guarantee, you can compile the C code to LLVM with `clang test.c -S --emit-llvm`
and compare the type definition yourself). G2W has to counterpart for the `size_t` type, so you will have to change between `u64` and `u32` to target 64-bit and 32-bit platforms.
Any standard libc functions can be used by declaring them as `extern`, with the exception of the `printf`-family of functions. Because G2W does not support variadic functions, the libc functions
`printf`, `sprintf`, `snprintf`, and `dprintf` are handled as special cases in the compiler, and do not need to be declared (`fprintf` is missing from this list because it requires a C `FILE*`, and there is no
way to include a C struct definition from a C header file).
