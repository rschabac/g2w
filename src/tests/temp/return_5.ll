target triple = "x86_64-unknown-linux"
declare i32 @printf(i8*, ...)
declare i32 @sprintf(i8*, i8*, ...)
declare i32 @snprintf(i8*, i64, i8*, ...)
declare i32 @dprintf(i32, i8*, ...)
declare i8* @malloc(i64)
declare void @free(i8*)
define i32 @main() {
	%_truncated179 = trunc i64 5 to i32
	ret i32 %_truncated179
}
