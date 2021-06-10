target triple = "x86_64-unknown-linux"
%vec_i32 = type {i32*, i64, i64}
@_string_literal_array60 = global [45 x i8] c"error, data is not null when capacity is 0%c\00"
@_string_literal_array168 = global [6 x i8] c"%ld%c\00"
declare i32 @printf(i8*, ...)
declare i32 @sprintf(i8*, i8*, ...)
declare i32 @snprintf(i8*, i64, i8*, ...)
declare i32 @dprintf(i32, i8*, ...)
declare i8* @malloc(i64)
declare void @free(i8*)
define %vec_i32 @vec_i32_new(i64 %_arg21) {
	%_arg_slot20 = alloca i64
	store i64 %_arg21, i64* %_arg_slot20
	%_result_loc22 = alloca %vec_i32
	%_capacity_loaded23 = load i64, i64* %_arg_slot20
	%_cmp24 = icmp ne i64 %_capacity_loaded23, 0
	br i1 %_cmp24, label %_then25, label %_else26
_then25:
	%_field28 = getelementptr %vec_i32, %vec_i32* %_result_loc22, i1 0, i32 0
	%_capacity_loaded29 = load i64, i64* %_arg_slot20
	%_sizeof30 = getelementptr i32, i32* null, i32 1
	%_sizeof_int31 = ptrtoint i32* %_sizeof30 to i64
	%_bool_op32 = mul i64 %_capacity_loaded29, %_sizeof_int31
	%_call33 = call i8* @malloc(i64 %_bool_op32)
	%_ptr_cast34 = bitcast i8* %_call33 to i32*
	store i32* %_ptr_cast34, i32** %_field28
	br label %_merge27
_else26:
	%_field35 = getelementptr %vec_i32, %vec_i32* %_result_loc22, i1 0, i32 0
	%_ptr_cast36 = bitcast i8* null to i32*
	store i32* %_ptr_cast36, i32** %_field35
	br label %_merge27
_merge27:
	%_field37 = getelementptr %vec_i32, %vec_i32* %_result_loc22, i1 0, i32 1
	store i64 0, i64* %_field37
	%_field38 = getelementptr %vec_i32, %vec_i32* %_result_loc22, i1 0, i32 2
	%_capacity_loaded39 = load i64, i64* %_arg_slot20
	store i64 %_capacity_loaded39, i64* %_field38
	%_result_loaded40 = load %vec_i32, %vec_i32* %_result_loc22
	ret %vec_i32 %_result_loaded40
}
define void @vec_i32_push(%vec_i32* %_arg42, i32 %_arg44) {
	%_arg_slot41 = alloca %vec_i32*
	store %vec_i32* %_arg42, %vec_i32** %_arg_slot41
	%_arg_slot43 = alloca i32
	store i32 %_arg44, i32* %_arg_slot43
	%_this_loaded45 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded46 = load %vec_i32, %vec_i32* %_this_loaded45
	%_extract47 = extractvalue %vec_i32 %_base_loaded46, 2
	%_cmp48 = icmp eq i64 %_extract47, 0
	br i1 %_cmp48, label %_then49, label %_else50
_then49:
	%_this_loaded52 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded53 = load %vec_i32, %vec_i32* %_this_loaded52
	%_extract54 = extractvalue %vec_i32 %_base_loaded53, 0
	%_ptr_cast55 = bitcast i8* null to i32*
	%_ptr_cmp56 = icmp ne i32* %_extract54, %_ptr_cast55
	br i1 %_ptr_cmp56, label %_then57, label %_else58
_then57:
	%_string_pointer61 = bitcast [45 x i8]* @_string_literal_array60 to i8*
	%_call62 = call i32 (i8*, ...) @printf(i8* %_string_pointer61, i64 10)
	br label %_merge59
_else58:
	br label %_merge59
_merge59:
	%_struct_deref63 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field64 = getelementptr %vec_i32, %vec_i32* %_struct_deref63, i1 0, i32 0
	%_sizeof65 = getelementptr i32, i32* null, i32 1
	%_sizeof_int66 = ptrtoint i32* %_sizeof65 to i64
	%_bool_op67 = mul i64 4, %_sizeof_int66
	%_call68 = call i8* @malloc(i64 %_bool_op67)
	%_ptr_cast69 = bitcast i8* %_call68 to i32*
	store i32* %_ptr_cast69, i32** %_field64
	%_struct_deref70 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field71 = getelementptr %vec_i32, %vec_i32* %_struct_deref70, i1 0, i32 0
	%_index_load72 = load i32*, i32** %_field71
	%_index_offset73 = getelementptr i32, i32* %_index_load72, i64 0
	%_e_loaded74 = load i32, i32* %_arg_slot43
	store i32 %_e_loaded74, i32* %_index_offset73
	%_struct_deref75 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field76 = getelementptr %vec_i32, %vec_i32* %_struct_deref75, i1 0, i32 2
	store i64 4, i64* %_field76
	%_struct_deref77 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field78 = getelementptr %vec_i32, %vec_i32* %_struct_deref77, i1 0, i32 1
	store i64 1, i64* %_field78
	br label %_merge51
_else50:
	br label %_merge51
_merge51:
	%_this_loaded79 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded80 = load %vec_i32, %vec_i32* %_this_loaded79
	%_extract81 = extractvalue %vec_i32 %_base_loaded80, 1
	%_this_loaded82 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded83 = load %vec_i32, %vec_i32* %_this_loaded82
	%_extract84 = extractvalue %vec_i32 %_base_loaded83, 2
	%_cmp85 = icmp eq i64 %_extract81, %_extract84
	br i1 %_cmp85, label %_then86, label %_else87
_then86:
	%_new_alloc_loc89 = alloca i32*
	%_this_loaded90 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded91 = load %vec_i32, %vec_i32* %_this_loaded90
	%_extract92 = extractvalue %vec_i32 %_base_loaded91, 2
	%_bool_op93 = mul i64 2, %_extract92
	%_call94 = call i8* @malloc(i64 %_bool_op93)
	%_ptr_cast95 = bitcast i8* %_call94 to i32*
	store i32* %_ptr_cast95, i32** %_new_alloc_loc89
	%_temp_loc96 = alloca i64
	store i64 0, i64* %_temp_loc96
	br label %_check_cond102
_check_cond102:
	%_temp_loaded97 = load i64, i64* %_temp_loc96
	%_this_loaded98 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded99 = load %vec_i32, %vec_i32* %_this_loaded98
	%_extract100 = extractvalue %vec_i32 %_base_loaded99, 1
	%_cmp101 = icmp ult i64 %_temp_loaded97, %_extract100
	br i1 %_cmp101, label %_body103, label %_after104
_body103:
	%_index_load105 = load i32*, i32** %_new_alloc_loc89
	%_temp_loaded106 = load i64, i64* %_temp_loc96
	%_index_offset107 = getelementptr i32, i32* %_index_load105, i64 %_temp_loaded106
	%_struct_deref108 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field109 = getelementptr %vec_i32, %vec_i32* %_struct_deref108, i1 0, i32 0
	%_index_load110 = load i32*, i32** %_field109
	%_temp_loaded111 = load i64, i64* %_temp_loc96
	%_index_offset112 = getelementptr i32, i32* %_index_load110, i64 %_temp_loaded111
	%_index_loaded113 = load i32, i32* %_index_offset112
	store i32 %_index_loaded113, i32* %_index_offset107
	br label %_check_cond102
_after104:
	%_this_loaded114 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded115 = load %vec_i32, %vec_i32* %_this_loaded114
	%_extract116 = extractvalue %vec_i32 %_base_loaded115, 0
	%_ptr_cast117 = bitcast i32* %_extract116 to i8*
	call void @free(i8* %_ptr_cast117)
	%_struct_deref119 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field120 = getelementptr %vec_i32, %vec_i32* %_struct_deref119, i1 0, i32 0
	%_new_alloc_loaded121 = load i32*, i32** %_new_alloc_loc89
	store i32* %_new_alloc_loaded121, i32** %_field120
	%_struct_deref122 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field123 = getelementptr %vec_i32, %vec_i32* %_struct_deref122, i1 0, i32 1
	%_this_loaded124 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded125 = load %vec_i32, %vec_i32* %_this_loaded124
	%_extract126 = extractvalue %vec_i32 %_base_loaded125, 1
	%_bool_op127 = add i64 %_extract126, 1
	store i64 %_bool_op127, i64* %_field123
	%_struct_deref128 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field129 = getelementptr %vec_i32, %vec_i32* %_struct_deref128, i1 0, i32 2
	%_this_loaded130 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded131 = load %vec_i32, %vec_i32* %_this_loaded130
	%_extract132 = extractvalue %vec_i32 %_base_loaded131, 2
	%_bool_op133 = mul i64 2, %_extract132
	store i64 %_bool_op133, i64* %_field129
	br label %_merge88
_else87:
	br label %_merge88
_merge88:
	%_struct_deref134 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field135 = getelementptr %vec_i32, %vec_i32* %_struct_deref134, i1 0, i32 0
	%_index_load136 = load i32*, i32** %_field135
	%_this_loaded137 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded138 = load %vec_i32, %vec_i32* %_this_loaded137
	%_extract139 = extractvalue %vec_i32 %_base_loaded138, 1
	%_index_offset140 = getelementptr i32, i32* %_index_load136, i64 %_extract139
	%_e_loaded141 = load i32, i32* %_arg_slot43
	store i32 %_e_loaded141, i32* %_index_offset140
	%_struct_deref142 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_field143 = getelementptr %vec_i32, %vec_i32* %_struct_deref142, i1 0, i32 1
	%_this_loaded144 = load %vec_i32*, %vec_i32** %_arg_slot41
	%_base_loaded145 = load %vec_i32, %vec_i32* %_this_loaded144
	%_extract146 = extractvalue %vec_i32 %_base_loaded145, 1
	%_bool_op147 = add i64 %_extract146, 1
	store i64 %_bool_op147, i64* %_field143
	ret void
}
define i32 @main() {
	%_v_loc148 = alloca %vec_i32
	%_call149 = call %vec_i32 @vec_i32_new(i64 5)
	store %vec_i32 %_call149, %vec_i32* %_v_loc148
	%_truncated150 = trunc i64 10 to i32
	call void @vec_i32_push(%vec_i32* %_v_loc148, i32 %_truncated150)
	%_truncated152 = trunc i64 11 to i32
	call void @vec_i32_push(%vec_i32* %_v_loc148, i32 %_truncated152)
	%_truncated154 = trunc i64 12 to i32
	call void @vec_i32_push(%vec_i32* %_v_loc148, i32 %_truncated154)
	%_truncated156 = trunc i64 13 to i32
	call void @vec_i32_push(%vec_i32* %_v_loc148, i32 %_truncated156)
	%_truncated158 = trunc i64 14 to i32
	call void @vec_i32_push(%vec_i32* %_v_loc148, i32 %_truncated158)
	%_index_loc160 = alloca i64
	store i64 0, i64* %_index_loc160
	br label %_check_cond165
_check_cond165:
	%_index_loaded161 = load i64, i64* %_index_loc160
	%_v_loaded162 = load %vec_i32, %vec_i32* %_v_loc148
	%_extract163 = extractvalue %vec_i32 %_v_loaded162, 1
	%_cmp164 = icmp ult i64 %_index_loaded161, %_extract163
	br i1 %_cmp164, label %_body166, label %_after167
_body166:
	%_string_pointer169 = bitcast [6 x i8]* @_string_literal_array168 to i8*
	%_field170 = getelementptr %vec_i32, %vec_i32* %_v_loc148, i1 0, i32 0
	%_index_load171 = load i32*, i32** %_field170
	%_index_loaded172 = load i64, i64* %_index_loc160
	%_index_offset173 = getelementptr i32, i32* %_index_load171, i64 %_index_loaded172
	%_index_loaded174 = load i32, i32* %_index_offset173
	%_call175 = call i32 (i8*, ...) @printf(i8* %_string_pointer169, i32 %_index_loaded174, i64 10)
	%_index_loaded176 = load i64, i64* %_index_loc160
	%_bool_op177 = add i64 %_index_loaded176, 1
	store i64 %_bool_op177, i64* %_index_loc160
	br label %_check_cond165
_after167:
	%_truncated178 = trunc i64 0 to i32
	ret i32 %_truncated178
}
