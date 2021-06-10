target triple = "x86_64-unknown-linux"
@_string_literal_array16 = global [14 x i8] c"Hello world%c\00"
declare i32 @printf(i8*, ...)
declare i32 @sprintf(i8*, i8*, ...)
declare i32 @snprintf(i8*, i64, i8*, ...)
declare i32 @dprintf(i32, i8*, ...)
declare i8* @malloc(i64)
declare void @free(i8*)
define i32 @main() {
	%_string_pointer17 = bitcast [14 x i8]* @_string_literal_array16 to i8*
	%_call18 = call i32 (i8*, ...) @printf(i8* %_string_pointer17, i64 10)
	%_truncated19 = trunc i64 0 to i32
	ret i32 %_truncated19
}
