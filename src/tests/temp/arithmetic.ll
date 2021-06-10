target triple = "x86_64-unknown-linux"
declare i32 @printf(i8*, ...)
declare i32 @sprintf(i8*, i8*, ...)
declare i32 @snprintf(i8*, i64, i8*, ...)
declare i32 @dprintf(i32, i8*, ...)
declare i8* @malloc(i64)
declare void @free(i8*)
define i32 @main() {
	%_x_loc1 = alloca i8
	%_y_loc2 = alloca i32
	%_truncated3 = trunc i64 6 to i8
	store i8 %_truncated3, i8* %_x_loc1
	%_truncated4 = trunc i64 9 to i32
	store i32 %_truncated4, i32* %_y_loc2
	%_x_loaded5 = load i8, i8* %_x_loc1
	%_truncated6 = trunc i64 10 to i8
	%_bool_op7 = add i8 %_x_loaded5, %_truncated6
	store i8 %_bool_op7, i8* %_x_loc1
	%_truncated8 = trunc i64 2 to i8
	%_x_loaded9 = load i8, i8* %_x_loc1
	%_bool_op10 = mul i8 %_truncated8, %_x_loaded9
	store i8 %_bool_op10, i8* %_x_loc1
	%_x_loaded11 = load i8, i8* %_x_loc1
	%_extended12 = sext i8 %_x_loaded11 to i32
	%_y_loaded13 = load i32, i32* %_y_loc2
	%_bool_op14 = add i32 %_extended12, %_y_loaded13
	store i32 %_bool_op14, i32* %_y_loc2
	%_y_loaded15 = load i32, i32* %_y_loc2
	ret i32 %_y_loaded15
}
