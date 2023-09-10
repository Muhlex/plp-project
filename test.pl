:- module(test, [
	mc_tests/0, mc_tests/1,
	mc_test/3, mc_test/4
]).

:- use_module(montecarlo).

/**
 * mc_tests is det
 *
 * Run manual tests.
 */
mc_tests :-
	mc_tests('./test').
/**
 * mc_tests(+Directory) is det
 *
 * Run manual tests, specifying the directory test files are contained in.
 */
mc_tests(Directory) :-
	directory_files(Directory, DirFilesRelative),
	add_directory(DirFilesRelative, Directory, DirFiles),
	include(exists_file, DirFiles, Files),
	maplist(consult, Files).
add_directory([], _Directory, []) :-
	!.
add_directory([File | RestFiles], Directory, [OutputFile | RestOutputFiles]) :-
	string_concat(Directory, "/", DirWithSlash),
	string_concat(DirWithSlash, File, OutputFile),
	add_directory(RestFiles, Directory, RestOutputFiles).

/**
 * mc_test(+File:file, :Query:atom, +ExpectedP:float, +Options:list) is det
 *
 * Run a single test. Arguments are shared with `montecarlo:montecarlo/4`, where the resulting
 * probability is replaced by the expected one for a successful test.
 */
mc_test(File, Query, ExpectedP, Options) :-
	writef('Testing file "%w" for query "%w"...\n', [File, Query]),
	format('Expected: ~w\n', [ExpectedP]),
	mc_test_single(File, Query, [sampler(standard)], Options),
	mc_test_single(File, Query, [sampler(gibbs)], Options),
	writeln(''),
	!.
/**
 * mc_test(+File:file, :Query:atom, +ExpectedP:float) is det
 *
 * Alias of `test:mc_test/4` with empty options.
 */
mc_test(File, Query, ExpectedP) :-
	mc_test(File, Query, ExpectedP, []).

mc_test_single(File, Query, Options, UserOptions) :-
	merge_options(UserOptions, [silent(1)], UserOpts),
	merge_options(Options, UserOpts, Opts),
	call_time(montecarlo(File, Query, ResultP, Opts), Benchmark),
	format(
		'  Result: ~4f  |  Inf.: ~t~D~36|  |  CPU: ~t~1fms~18+  |  ~w\n',
		[ResultP, Benchmark.get(inferences), Benchmark.get(cpu) * 1000, Options]
	).
