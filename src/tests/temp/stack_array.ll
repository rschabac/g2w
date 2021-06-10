target triple = "x86_64-unknown-linux"
@_string_literal_array188 = global [5 x i8] c"%d, \00"
@_string_literal_array197 = global [3 x i8] c"%c\00"
@_string_literal_array208 = global [5 x i8] c"%d, \00"
@_string_literal_array218 = global [3 x i8] c"%c\00"
@_string_literal_array229 = global [5 x i8] c"%d, \00"
@_string_literal_array238 = global [3 x i8] c"%c\00"
declare i32 @printf(i8*, ...)
declare i32 @sprintf(i8*, i8*, ...)
declare i32 @snprintf(i8*, i64, i8*, ...)
declare i32 @dprintf(i32, i8*, ...)
declare i8* @malloc(i64)
declare void @free(i8*)
define void @print_array_of_5_i32_by_value([5 x i32] %_arg181) {
	%_arg_slot180 = alloca [5 x i32]
	store [5 x i32] %_arg181, [5 x i32]* %_arg_slot180
	%_i_loc182 = alloca i64
	store i64 0, i64* %_i_loc182
	br label %_check_cond185
_check_cond185:
	%_i_loaded183 = load i64, i64* %_i_loc182
	%_cmp184 = icmp slt i64 %_i_loaded183, 5
	br i1 %_cmp184, label %_body186, label %_after187
_body186:
	%_string_pointer189 = bitcast [5 x i8]* @_string_literal_array188 to i8*
	%_arr_decay190 = bitcast [5 x i32]* %_arg_slot180 to i32*
	%_i_loaded191 = load i64, i64* %_i_loc182
	%_index_offset192 = getelementptr i32, i32* %_arr_decay190, i64 %_i_loaded191
	%_index_loaded193 = load i32, i32* %_index_offset192
	%_call194 = call i32 (i8*, ...) @printf(i8* %_string_pointer189, i32 %_index_loaded193)
	%_i_loaded195 = load i64, i64* %_i_loc182
	%_bool_op196 = add i64 %_i_loaded195, 1
	store i64 %_bool_op196, i64* %_i_loc182
	br label %_check_cond185
_after187:
	%_string_pointer198 = bitcast [3 x i8]* @_string_literal_array197 to i8*
	%_call199 = call i32 (i8*, ...) @printf(i8* %_string_pointer198, i64 10)
	ret void
}
define void @print_array_of_5_i32_by_pointer_to_array([5 x i32]* %_arg201) {
	%_arg_slot200 = alloca [5 x i32]*
	store [5 x i32]* %_arg201, [5 x i32]** %_arg_slot200
	%_i_loc202 = alloca i64
	store i64 0, i64* %_i_loc202
	br label %_check_cond205
_check_cond205:
	%_i_loaded203 = load i64, i64* %_i_loc202
	%_cmp204 = icmp slt i64 %_i_loaded203, 5
	br i1 %_cmp204, label %_body206, label %_after207
_body206:
	%_string_pointer209 = bitcast [5 x i8]* @_string_literal_array208 to i8*
	%_arr_loaded210 = load [5 x i32]*, [5 x i32]** %_arg_slot200
	%_arr_decay211 = bitcast [5 x i32]* %_arr_loaded210 to i32*
	%_i_loaded212 = load i64, i64* %_i_loc202
	%_index_offset213 = getelementptr i32, i32* %_arr_decay211, i64 %_i_loaded212
	%_index_loaded214 = load i32, i32* %_index_offset213
	%_call215 = call i32 (i8*, ...) @printf(i8* %_string_pointer209, i32 %_index_loaded214)
	%_i_loaded216 = load i64, i64* %_i_loc202
	%_bool_op217 = add i64 %_i_loaded216, 1
	store i64 %_bool_op217, i64* %_i_loc202
	br label %_check_cond205
_after207:
	%_string_pointer219 = bitcast [3 x i8]* @_string_literal_array218 to i8*
	%_call220 = call i32 (i8*, ...) @printf(i8* %_string_pointer219, i64 10)
	ret void
}
define void @print_array_of_5_i32_by_pointer_to_i32(i32* %_arg222) {
	%_arg_slot221 = alloca i32*
	store i32* %_arg222, i32** %_arg_slot221
	%_i_loc223 = alloca i64
	store i64 0, i64* %_i_loc223
	br label %_check_cond226
_check_cond226:
	%_i_loaded224 = load i64, i64* %_i_loc223
	%_cmp225 = icmp slt i64 %_i_loaded224, 5
	br i1 %_cmp225, label %_body227, label %_after228
_body227:
	%_string_pointer230 = bitcast [5 x i8]* @_string_literal_array229 to i8*
	%_index_load231 = load i32*, i32** %_arg_slot221
	%_i_loaded232 = load i64, i64* %_i_loc223
	%_index_offset233 = getelementptr i32, i32* %_index_load231, i64 %_i_loaded232
	%_index_loaded234 = load i32, i32* %_index_offset233
	%_call235 = call i32 (i8*, ...) @printf(i8* %_string_pointer230, i32 %_index_loaded234)
	%_i_loaded236 = load i64, i64* %_i_loc223
	%_bool_op237 = add i64 %_i_loaded236, 1
	store i64 %_bool_op237, i64* %_i_loc223
	br label %_check_cond226
_after228:
	%_string_pointer239 = bitcast [3 x i8]* @_string_literal_array238 to i8*
	%_call240 = call i32 (i8*, ...) @printf(i8* %_string_pointer239, i64 10)
	ret void
}
define i32 @main() {
	%_arr_loc241 = alloca [5 x i32]
	%_arr_decay242 = bitcast [5 x i32]* %_arr_loc241 to i32*
	%_index_offset243 = getelementptr i32, i32* %_arr_decay242, i64 0
	%_truncated244 = trunc i64 1 to i32
	store i32 %_truncated244, i32* %_index_offset243
	%_arr_decay245 = bitcast [5 x i32]* %_arr_loc241 to i32*
	%_index_offset246 = getelementptr i32, i32* %_arr_decay245, i64 1
	%_truncated247 = trunc i64 2 to i32
	store i32 %_truncated247, i32* %_index_offset246
	%_arr_decay248 = bitcast [5 x i32]* %_arr_loc241 to i32*
	%_index_offset249 = getelementptr i32, i32* %_arr_decay248, i64 2
	%_truncated250 = trunc i64 4 to i32
	store i32 %_truncated250, i32* %_index_offset249
	%_arr_decay251 = bitcast [5 x i32]* %_arr_loc241 to i32*
	%_index_offset252 = getelementptr i32, i32* %_arr_decay251, i64 3
	%_truncated253 = trunc i64 8 to i32
	store i32 %_truncated253, i32* %_index_offset252
	%_arr_decay254 = bitcast [5 x i32]* %_arr_loc241 to i32*
	%_index_offset255 = getelementptr i32, i32* %_arr_decay254, i64 4
	%_truncated256 = trunc i64 16 to i32
	store i32 %_truncated256, i32* %_index_offset255
	%_arr_loaded257 = load [5 x i32], [5 x i32]* %_arr_loc241
	call void @print_array_of_5_i32_by_value([5 x i32] %_arr_loaded257)
	call void @print_array_of_5_i32_by_pointer_to_array([5 x i32]* %_arr_loc241)
	%_arr_decay260 = bitcast [5 x i32]* %_arr_loc241 to i32*
	%_index_offset261 = getelementptr i32, i32* %_arr_decay260, i64 0
	call void @print_array_of_5_i32_by_pointer_to_i32(i32* %_index_offset261)
	%_truncated263 = trunc i64 0 to i32
	ret i32 %_truncated263
}
