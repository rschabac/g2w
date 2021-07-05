#[macro_use]
extern crate lalrpop_util;
extern crate clap;
extern crate tempfile;
mod ast;
mod typechecker;
mod llvm;

mod frontend;
use std::time::{Instant, Duration};

//This seems to prevent clippy from checking the generated parser file
lalrpop_mod!(#[allow(clippy::all)] pub parser);

#[cfg(test)]
mod tests;

#[allow(dead_code)]
#[derive(Debug)]
enum OptLevel {
	O0,
	O1,
	O2,
	O3,
	Osize
}
impl OptLevel {
	fn to_clang_arg_str(&self) -> &'static str {
		use OptLevel::*;
		match self {
			O0 => "-O0",
			O1 => "-O1",
			O2 => "-O2",
			O3 => "-O3",
			Osize => "-Os"
		}
	}
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq)]
enum Phase {
	Check,		//parse and typecheck
	Frontend,	//compile to llvm ir, yields a .ll file
	Backend,	//compile llvm ir to asm, yields a .s file
	Assemble,	//assemble asm to object file, yields a .o file
	Link		//link object file(s), yields an executable
}
impl Phase {
	fn get_default_output_filename(&self) -> &'static str {
		use Phase::*;
		match self {
			Check => "check_phase_should_not_output_file",
			Frontend => "output.ll",
			Backend => "output.s",
			Assemble => "output.o",
			Link => "a.out"
		}
	}
}

#[allow(dead_code)]
#[derive(Debug)]
struct Opts<'a> {
	target_triple: &'a str,
	errno_func_name: &'a str,
	opt_level: OptLevel,
	last_phase: Phase,
	output_file_name: &'a str,
	print_timings: bool,
}


fn get_opt_level(matches: &clap::ArgMatches) -> OptLevel {
	use OptLevel::*;
	if matches.is_present("opt-level-0") {
		return O0;
	}
	if matches.is_present("opt-level-1") {
		return O1;
	}
	if matches.is_present("opt-level-2") {
		return O2;
	}
	if matches.is_present("opt-level-3") {
		return O3;
	}
	if matches.is_present("opt-level-size") {
		return Osize;
	}
	O0
}

fn get_last_phase(matches: &clap::ArgMatches) -> Phase {
	use Phase::*;
	if matches.is_present("check") {
		return Check;
	}
	if matches.is_present("frontend") {
		return Frontend;
	}
	if matches.is_present("backend") {
		return Backend;
	}
	if matches.is_present("assemble") {
		return Assemble;
	}
	Link
}

struct Timing {
	start_time: Instant,
	arg_parse: (Instant, Instant),
	read_input: (Instant, Instant),
	parsing: (Instant, Instant),
	typechecking: (Instant, Instant),
	frontend: Option<(Instant, Instant)>,
	write_output: Option<(Instant, Instant)>,
	clang: Option<(Instant, Instant)>,
	end_time: Instant,
}

fn with_timing() -> Result<Option<Timing>, String>{
	let mut timeinfo = Timing{
		start_time: Instant::now(),
		arg_parse: (Instant::now(), Instant::now()),
		read_input: (Instant::now(), Instant::now()),
		parsing: (Instant::now(), Instant::now()), //will be overridden later
		typechecking: (Instant::now(), Instant::now()), //will be overridden later
		frontend: None,
		write_output: None,
		clang: None,
		end_time: Instant::now() //will be overridden later
	};
	use clap::{Arg, ArgGroup, app_from_crate, crate_name, crate_version, crate_authors, crate_description};
	timeinfo.arg_parse.0 = Instant::now();
	let matches = app_from_crate!()
		.arg(
			Arg::with_name("target-triple")
				.long("target-triple")
				.value_name("TRIPLE")
				.takes_value(true)
				.help("The target triple Clang/llvm should use")
				.long_help(
					"The target triple that Clang/llvm should use when compiling the files. \
					You can find the target triple for a given machine by running 'clang -dumpmachine' \
					When left blank or set to 'native', the target triple will be obtained by running 'clang -dumpmachine'"
				)
				.default_value("native")
		)
		.arg(
			Arg::with_name("errno-location")
				.long("errno-location")
				.value_name("FUNCTION_NAME")
				.takes_value(true)
				.help("The name of the function that should be called to get the errno value")
				.long_help(
					"On most systems, errno is defined as a macro that expands to something like (*__errno_location()). \
					On most versions of glibc and musl, the name of the hidden function is '__errno_location'. If this \
					is not the case for you, you can use this option to set a different name"
				)
				.default_value("__errno_location")
		)
		.arg(
			Arg::with_name("time")
				.long("time")
				.help("Print the time taken for each phase of compilation to standard output")
		)
		.arg(
			Arg::with_name("output-file-name")
				.long("output")
				.short("o")
				.takes_value(true)
				.value_name("FILE")
				.help("Write output to file")
				.long_help(
					"Specify the name of the file the output of compiling all .src files should be written to. \
					This will default to one of the following names, depending on what the final phase of compilation is:\n\
					- 'output.ll' if only running the frontend phase (--emit-llvm)\n\
					- 'output.s'  if running the frontend and backend phases (-S)\n\
					- 'output.o'  if running the frontend, backend, and assembly phases (-c)\n\
					- 'a.out'     if running all phases (no command line flag)\n\
					If the --check flag is passed, no output is necessary, and this option is unused."
				)
		)
		.arg(
			Arg::with_name("opt-level-0")
				.long("O0")
				.help("No optimization, fastest compile times")
		)
		.arg(
			Arg::with_name("opt-level-1")
				.long("O")
				.alias("O1")
				.help("Somewhere between --O0 and --O2")
		)
		.arg(
			Arg::with_name("opt-level-2")
				.long("O2")
				.help("Moderate level of optimization")
		)
		.arg(
			Arg::with_name("opt-level-3")
				.long("O3")
				.help("Like --O2, but enables optimizations that may increase compile times/binary size")
		)
		.arg(
			Arg::with_name("opt-level-size")
				.long("Os")
				.alias("Osize")
				.help("Like --O2, but with extra optimizations to reduce the binary size")
		)
		.group(
			ArgGroup::with_name("opt-level")
				.args(&["opt-level-0", "opt-level-1", "opt-level-2", "opt-level-3", "opt-level-size"])
		)
		.arg(
			Arg::with_name("check")
				.long("check")
				.help("Only check the .src files for syntax/type errors, do not output anything")
				.long_help(
					"Check the given .src files for syntax/type errors, but do not compile them. \
					Note: if any other file types are provided, they will be ignored."
				)
		)
		.arg(
			Arg::with_name("frontend")
				.long("emit-llvm")
				.help("Run the frontend phase of compilation on the .src files, yielding a single .ll file")
		)
		.arg(
			Arg::with_name("backend")
				.short("S")
				.help("Run the backend phase of compilation on the input files, yielding .s file(s)")
		)
		.arg(
			Arg::with_name("assemble")
				.short("c")
				.help("Run the assembly phase of compilation on the input files, yielding .o file(s)")
		)
		.group(
			ArgGroup::with_name("last_phase")
				.args(&["check", "frontend", "backend", "assemble"])
		)
		.arg(
			Arg::with_name("input_files")
				.help("Input files to compile")
				.long_help( concat!(
					"Input files to be processed. The type of the file is determined by its extension, and can be one of the following:\n\
					- .src  Source code\n\
					- .c    C code\n\
					- .ll   LLVM intermediate representation, in a human-readable form\n\
					- .bc   LLVM intermediate representation, in a machine-readable form\n\
					- .s    Assembly code\n\
					- .o    Object files\n\
					Any files that are not relevant in the requested phases of compilation will be ignored.\n\
					Example: '", crate_name!(), " main.src lib.c does/not/exist.o -c' will ignore does/not/exist.o, since the \
					linking phase is not being run."
					)
				)
				.multiple(true)
				.index(1)
		)
		.get_matches();
	let last_phase = get_last_phase(&matches);
	let options = Opts {
		target_triple: {
			let s = matches.value_of("target-triple").unwrap();
			if s == "native" {
				match frontend::get_native_target_triple() {
					Ok(s) => s,
					Err((err_msg, clang_stderr)) => {
						eprintln!("Could not get native target triple:\n{}\n", err_msg);
						std::io::stderr().write_all(&clang_stderr).map_err(|e| e.to_string())?;
						std::process::exit(1)
					}
				}
			} else {
				s
			}
		},
		errno_func_name: matches.value_of("errno-location").unwrap_or("__errno_location"),
		opt_level: get_opt_level(&matches),
		last_phase,
		output_file_name: matches.value_of("output-file-name").unwrap_or_else(|| last_phase.get_default_output_filename()),
		print_timings: matches.is_present("time")
	};
	let input_file_names = matches.values_of("input_files").ok_or_else(|| {
		"No input files provided".to_owned()
	})?;
	timeinfo.arg_parse.1 = Instant::now();
	timeinfo.read_input.0 = timeinfo.arg_parse.1;
	let mut c_file_names = Vec::new();
	let mut ll_and_bc_file_names = Vec::new();
	let mut asm_file_names = Vec::new();
	let mut obj_file_names = Vec::new();
	let mut combined_src = String::new();
	//TODO: need to read each file individually in order to get line/col info, once lexer/parser is better
	for filename in input_file_names {
		if filename.ends_with(".c") {
			c_file_names.push(filename);
			continue
		}
		if filename.ends_with(".ll") || filename.ends_with(".bc") {
			ll_and_bc_file_names.push(filename);
			continue
		}
		if filename.ends_with(".s") {
			asm_file_names.push(filename);
			continue
		}
		if filename.ends_with(".o") {
			obj_file_names.push(filename);
			continue
		}
		if !filename.ends_with(".src") {
			return Err(format!("unknown file extension, cannot process file {}", filename));
		}
		use std::fs::*;
		let mut src_file: File = File::open(filename).map_err(|e| {
			format!("Could not open input file {}: {}", filename, e)
		})?;
		use std::io::Read;
		src_file.read_to_string(&mut combined_src).map_err(|e| {
			format!("Could not read file {}: {}", filename, e)
		})?;
	}
	let multiple_output_files: bool = ll_and_bc_file_names.len() + asm_file_names.len() + obj_file_names.len() + if combined_src.is_empty() {0} else {1} >= 2;
	if multiple_output_files && matches.is_present("output-file-name") {
		return Err("Cannot specify an output file name when generating multiple output files".to_owned());
	}
	timeinfo.read_input.1 = Instant::now();
	timeinfo.parsing.0 = timeinfo.read_input.1;
	let program_parser = parser::ProgramParser::new();
	let ast: Vec<ast::Gdecl> = program_parser.parse(combined_src.as_str()).map_err(|e| {
		format!("Parse error: {}", e)
	})?;
	timeinfo.parsing.1 = Instant::now();
	timeinfo.typechecking.0 = timeinfo.parsing.1;
	let program_context = typechecker::typecheck_program(&ast).map_err(|err_msg| {
		format!("Type Error: {}", err_msg)
	})?;
	timeinfo.typechecking.1 = Instant::now();
	if last_phase == Phase::Check {
		timeinfo.end_time = Instant::now();
		if options.print_timings {
			return Ok(Some(timeinfo));
		} else {
			return Ok(None);
		}
	}
	timeinfo.frontend = Some((timeinfo.typechecking.1, Instant::now()));
	let llvm_prog = frontend::cmp_prog(&ast.into(), &program_context, options.target_triple, options.errno_func_name);
	timeinfo.frontend.as_mut().unwrap().1 = Instant::now();
	timeinfo.write_output = Some((timeinfo.frontend.unwrap().1, Instant::now()));
	use std::io::Write;
	if last_phase == Phase::Frontend {
		use std::fs::OpenOptions;
		let mut output_ll_file = OpenOptions::new().read(true).write(true).create(true).truncate(true)
			.open(&options.output_file_name).map_err(|e| format!("Could not open output file {}: {}", &options.output_file_name, e))?;
		write!(output_ll_file, "{}", llvm_prog).map_err(|e| format!("IO error writing to ll file: {}", e))?;
		timeinfo.write_output.as_mut().unwrap().1 = Instant::now();
		timeinfo.end_time = timeinfo.write_output.unwrap().1;
		if options.print_timings {
			return Ok(Some(timeinfo));
		} else {
			return Ok(None);
		}
	}
	//let mut output_ll_file = tempfile::tempfile().map_err(|e| format!("Could not create temporary ll file: {}", e))?;
	let mut output_ll_file = tempfile::Builder::new()
		.prefix("output")
		.suffix(".ll")
		.rand_bytes(0)
		.tempfile()
		.map_err(|e| format!("Could not create temporary ll file: {}", e))?;
	write!(output_ll_file, "{}", llvm_prog).map_err(|e| format!("IO error writing to temporary ll file: {}", e))?;
	timeinfo.write_output.as_mut().unwrap().1 = Instant::now();
	timeinfo.clang = Some((timeinfo.write_output.unwrap().1, Instant::now()));
	use std::process::Command;
	let clang_exit_status = match last_phase {
		Phase::Backend => {
			//clang {opt_level} -o {output_file} --target={target_triple} {.c, .ll and .bc files} -S -x ir -
			let mut command = Command::new("clang");
			command
				.arg(options.opt_level.to_clang_arg_str())
				.arg(format!("--target={}", options.target_triple))
				.args(c_file_names.iter().chain(ll_and_bc_file_names.iter()))
				.arg(output_ll_file.path())
				.arg("-S");
			if !multiple_output_files {
				command.arg("-o").arg(options.output_file_name);
			}
			command.status()
		},
		Phase::Assemble => {
			//clang {opt_level} -o {output_file} --target={target_triple} {.c, .ll, .bc, and .s files} -c -x ir -
			let mut command = Command::new("clang");
			command
				.arg(options.opt_level.to_clang_arg_str())
				.arg(format!("--target={}", options.target_triple))
				.args(c_file_names.iter().chain(ll_and_bc_file_names.iter()).chain(asm_file_names.iter()))
				.arg(output_ll_file.path())
				.arg("-c");
			if !multiple_output_files {
				command.arg("-o").arg(options.output_file_name);
			}
			command.status()
		},
		Phase::Link => {
			//clang {opt_level} -o {output_file} --target={target_triple} {all other file names} -x ir -
			Command::new("clang")
				.arg(options.opt_level.to_clang_arg_str())
				.arg("-o")
				.arg(options.output_file_name)
				.arg(format!("--target={}", options.target_triple))
				.args(c_file_names.iter().chain(ll_and_bc_file_names.iter()).chain(asm_file_names.iter()).chain(obj_file_names.iter()))
				.arg(output_ll_file.path())
				.status()
		},
		Phase::Check | Phase::Frontend => panic!("Should have been caught by now")
	}.map_err(|e| format!("Could not execute clang: {}", e))?;
	if !clang_exit_status.success() {
		return Err("clang failed".to_owned());
	}
	timeinfo.clang.as_mut().unwrap().1 = Instant::now();
	timeinfo.end_time = timeinfo.clang.unwrap().1;
	if options.print_timings {
		return Ok(Some(timeinfo));
	} else {
		return Ok(None);
	}
}

fn main() -> Result<(), String> {
	let timeinfo = with_timing()?;
	if timeinfo.is_none() {
		//the --time flag was not used, don't print time info
		return Ok(());
	}
	let timeinfo = timeinfo.unwrap();
	let overall_duration = timeinfo.end_time - timeinfo.start_time;
	let arg_parse_duration = timeinfo.arg_parse.1 - timeinfo.arg_parse.0;
	let read_input_duration = timeinfo.read_input.1 - timeinfo.read_input.0;
	let parse_duration = timeinfo.parsing.1 - timeinfo.parsing.0;
	let typechecking_duration = timeinfo.typechecking.1 - timeinfo.typechecking.0;
	let frontend_duration = timeinfo.frontend.map(|(start, end)| end - start);
	let write_output_duration = timeinfo.write_output.map(|(start, end)| end - start);
	let clang_duration = timeinfo.clang.map(|(start, end)| end - start);
	let measured_durations = [arg_parse_duration, read_input_duration, parse_duration, typechecking_duration, frontend_duration.unwrap_or_default(), write_output_duration.unwrap_or_default(), clang_duration.unwrap_or_default()];
	let other_duration = overall_duration - measured_durations.iter().sum();
	let seconds_width = if overall_duration.as_secs() == 0 {1usize} else {((overall_duration.as_secs() as f32).log10().floor() as usize) + 1};
	/*
	1.234s (32.1%) parsing
	5.432s ( 4.1%) typechecking
	0.000s ( 0.0%) frontend (not executed)
	*/
	//println!("{:width$}", 23.456, width = 3);
	let print_duration = |d: &Duration, s: &str| {
		let percentage = d.as_secs_f64() / overall_duration.as_secs_f64() * 100f64;
		let int_part = percentage.trunc() as u64;
		let frac_part = (percentage.fract() * 1000f64) as u64;
		println!("{:width$}.{:03}s ({:2}.{:03}%) {}", d.as_secs(), d.as_millis(), int_part, frac_part, s, width = seconds_width);
	};
	print_duration(&arg_parse_duration, "command-line argument parsing");
	print_duration(&read_input_duration, "reading input files");
	print_duration(&parse_duration, "parsing");
	print_duration(&typechecking_duration, "typechecking");
	if let Some(frontend_duration) = frontend_duration {
		print_duration(&frontend_duration, "frontend");
	} else {
		println!("0.000s ( 0.0%) frontend (not executed)");
	}
	if let Some(write_output_duration) = write_output_duration {
		print_duration(&write_output_duration, "write_output");
	} else {
		println!("0.000s ( 0.0%) write_output (not executed)");
	}
	if let Some(clang_duration) = clang_duration {
		print_duration(&clang_duration, "clang");
	} else {
		println!("0.000s ( 0.000%) clang (not executed)");
	}
	print_duration(&other_duration, "other");
	println!("{:width$}.{:03}s           total", overall_duration.as_secs(), overall_duration.as_millis(), width = seconds_width);
	Ok(())
}
