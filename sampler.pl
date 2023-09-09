:- module(sampler, [
	load_program/1,
	unload_program/0,
	sample_goal/1,
	sample_goal_gibbs/2,
	op(1120, xf, <---),
	op(1120, xfx, <---),
	op(1080, xfy, ::)
]).

:- dynamic(transformed:(<---)/1).
:- dynamic(transformed:(<---)/2).
:- multifile(transformed:(<---)/1).
:- multifile(transformed:(<---)/2).

:- dynamic((::)/2).
:- dynamic(transformed:samp/3).
:- dynamic(transformed:sampled/3).

/**
 * load_program(:File:file) is det
 *
 * Load the PLP under the given File source and transform it's content for future sampling.
 */
load_program(File) :-
	transformed:load_files(File), % using `transformed` as a namespace to scope the transformed program
	findall(Head <--- Body, transformed:(Head <--- Body), Clauses, ClausesTail),
	findall(Head <--- [], transformed:(Head <---), ClausesTail),
	maplist(body2list, Clauses, Clauses2),
	maplist(resolve_disjunct_heads, Clauses2, ClausesPerDisjunction), % returns nested list
	maplist(get_disjunction_weights, ClausesPerDisjunction, WeightsPerDisjunction),
	assert_disjunctions(ClausesPerDisjunction, WeightsPerDisjunction).

/**
 * Parse disjunctions in a clause's head by transforming it into a list of clauses instead,
 *	with one element of the disjunction as each new clause's head:
 *	0.5::reallycold; 0.5::freezing <--- [cold]
 *	↓
 *	[0.5::reallycold <--- [cold], 0.5::freezing <--- [cold]]
 */
resolve_disjunct_heads((Head; RestHeads <--- Body), [Head <--- Body | Rest]) :-
	resolve_disjunct_heads(RestHeads <--- Body, Rest),
	!.
resolve_disjunct_heads(LastHead <--- Body, [LastHead <--- Body | []]).

/*
	Write the weights of all clauses inside a disjunction into a list,
	adding a null weight when they don't add up to 1.0.
*/
get_disjunction_weights(Disjunction, Weights) :-
	get_disjunction_weights(Disjunction, Weights, 0).
get_disjunction_weights([Weight::_Head <--- _Body | RestClauses], [Weight | RestWeights], TotalWeight) :-
	NewTotalWeight is TotalWeight + Weight,
	get_disjunction_weights(RestClauses, RestWeights, NewTotalWeight),
	!.
get_disjunction_weights([], NullWeightList, TotalWeight) :- % conditionally add null weight
	(TotalWeight < 1.0 ->
		NullWeightList = [1.0 - TotalWeight | []]
	;
		NullWeightList = []
	).

% Loop disjunctions, keeping track of their indices.
assert_disjunctions(ClausesPerDisjunction, WeightsPerDisjunction) :-
	assert_disjunctions(ClausesPerDisjunction, WeightsPerDisjunction, 0).
assert_disjunctions([Disjunction | RestDisjunctions], [Weights | RestWeights], CurrDisjunctionIndex) :-
	assert_disjunction(Disjunction, Weights, CurrDisjunctionIndex),
	NewDisjunctionIndex is CurrDisjunctionIndex + 1,
	assert_disjunctions(RestDisjunctions, RestWeights, NewDisjunctionIndex),
	!.
assert_disjunctions([], [], _DisjunctionIndex).

% Loop clauses inside disjunction, keeping track of the clause indices
% (matching the original head indices of the combined disjunctive clause).
assert_disjunction(Disjunctions, Weights, DisjunctionIndex) :-
	assert_disjunction(Disjunctions, Weights, DisjunctionIndex, 0).
assert_disjunction([Clause | RestClauses], Weights, DisjunctionIndex, CurrHeadIndex) :-
	assert_clause(Clause, Weights, DisjunctionIndex, CurrHeadIndex),
	NewHeadIndex is CurrHeadIndex + 1,
	assert_disjunction(RestClauses, Weights, DisjunctionIndex, NewHeadIndex),
	!.
assert_disjunction([], _Weights, _DisjunctionIndex, _CurrHeadIndex).

/*
	Given a single PLP clause, transform it into an equivalent standard Prolog clause
	according to the transformation rules detailed in Riguzzi 2013, p. 7.
*/
assert_clause(_Weight::Head <--- [], Weights, DisjunctionIndex, HeadIndex) :-
	Transformed = (Head :- (sampler:sample_head(Weights, DisjunctionIndex, [], NH), NH = HeadIndex)),
	assert_transformed(Transformed).
assert_clause(_Weight::Head <--- [BodyHead | BodyRest], Weights, DisjunctionIndex, HeadIndex) :-
	Body = [BodyHead | BodyRest],
	maplist(term_variables, Body, ConjunctionsVariables),
	flatten(ConjunctionsVariables, Variables),
	list_to_conjunction(Body, BodyConjunction),
	Transformed = (Head :- (BodyConjunction, sampler:sample_head(Weights, DisjunctionIndex, Variables, NH), NH = HeadIndex)),
	generate_clause_samp(Weights, DisjunctionIndex, Variables, Generated),
	assert_transformed(Transformed),
	transformed:assertz(Generated).

assert_transformed(Predicate) :-
	(Head :- _) = Predicate,
	functor(Head, HeadName, HeadArity),
	transformed:dynamic(HeadName/HeadArity), % make sure we are allowed to add to the predicate
	transformed:assertz(Predicate).

generate_clause_samp(Weights, DisjunctionIndex, Variables, Samp) :-
	Samp = (samp(DisjunctionIndex, Variables, Val) :- (sampler:sample_head(Weights, DisjunctionIndex, Variables, Val)) ).

/*
	Transform a list of terms extracted from an object program's clause
	into a standard prolog conjunction.
*/
list_to_conjunction([Term], Term) :-
	!.
list_to_conjunction([Term | Rest], ','(Term, Conjunction)) :-
	list_to_conjunction(Rest, Conjunction).


% Helper method for alternative syntax.
body2list(Head <--- Body, ListBody) :- is_list(Body), ListBody = (Head <--- Body).
body2list(Head <--- Body, ListBody) :- (\+ is_list(Body)), ListBody = (Head <--- [Body]).

/**
 * unload_program is det
 *
 * Cleanup environment state (usually after running a sampling process to completion).
 */
unload_program :-
	find_loaded_predicates(Predicates),
	maplist(transformed:abolish, Predicates).

find_loaded_predicates(Predicates) :-
	findall(Predicate, current_predicate(transformed:Predicate), PredicatesAll),
	exclude(is_lpad_operator, PredicatesAll, Predicates).
is_lpad_operator((<---)/_).



/*
	Generate a sample for a head, given its respective weights.
*/
sample_head(_Weights, RequiredHead, Variables, HeadId) :-
	transformed:sampled(RequiredHead, Variables, HeadId), !.

sample_head(Weights, RequiredHead, Variables, HeadId) :-
	sample(Weights, HeadId),
	transformed:assertz(sampled(RequiredHead, Variables, HeadId)).



sample(Weights, HeadId) :-
	random(Prob),
	sample(Weights, 0, 0, Prob, HeadId).

sample([HeadProb | Tail], Index, Prev, Prob, HeadId) :-
	Succ is Index + 1,
	Next is Prev + HeadProb,
	(Prob =< Next ->
		HeadId = Index
	;
		sample(Tail, Succ, Next, Prob, HeadId)
	).

/**
 * sample_goal(:Goal:atom) is det
 *
 * Assuming a suitable object program has already been transformed via load_program,
 * take a sample of the given Query.
 *
 */
sample_goal(Goal) :-
	abolish_all_tables,
	clear_recorded_samples,
	transformed:call(Goal).



/**
 * sample_goal_gibbs(+BlockSize:int,:Query:atom) is det
 *
 * Assuming a suitable object program has already been transformed via load_program,
 * take a sample of the given Query via Gibbs-Sampling as detailed in https://ceur-ws.org/Vol-2678/paper12.pdf.
 */
sample_goal_gibbs(BlockSize, Query) :-
	remove_samples(BlockSize, Removed),
	transformed:call(Query),
	ensure_sampled(Removed).

remove_samples(Block, Samp) :- remove_samp(Block, Samp); Samp = [].

remove_samp(0, []) :- !.
remove_samp(Block, [(RequiredHead, Variables) | Samp]) :-
	transformed:retract(sampled(RequiredHead, Variables, _)),!,
	RemainingBlock is Block - 1,
	remove_samp(RemainingBlock, Samp).

ensure_sampled(S) :- maplist(check_sam, S).

check_sam((RequiredHead, Variables)) :- transformed:samp(RequiredHead, Variables, _).



clear_recorded_samples :- transformed:retractall(sampled(_, _, _)).

/*
	Erase all previously recorded sample entries from the database.
*/
clear_recorded_pl_heads :-
	findall(DbReference, recorded(samples, _, DbReference), References),
	erase_all_references(References).

erase_all_references([]).
erase_all_references([Reference | Rest]) :-
	erase(Reference), erase_all_references(Rest).
