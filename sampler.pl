:- module(sampler, [
	load_program/1,
	unload_program/0,
	sample_goal/1,
	sample_goal_gibbs/1,
	op(1120, xfx, <---),
	op(1080, xfy, ::)
]).

:- dynamic(transformed:(<---)/2).
:- dynamic((::)/2).
:- dynamic(transformed:samp/3).

/*
	Load the PLP under the given [File] source and transform it's content for future sampling.
*/
load_program(File) :-
	transformed:consult(File), % using `transformed` as a namespace to scope the transformed program
	findall(Head <--- Body, transformed:(Head <--- Body), Clauses),
	maplist(resolve_disjunct_heads, Clauses, ClausesPerDisjunction), % returns nested list
	maplist(get_disjunction_weights, ClausesPerDisjunction, WeightsPerDisjunction),
	assert_disjunctions(ClausesPerDisjunction, WeightsPerDisjunction).

/*
	Parse disjunctions in a clause's head by transforming it into a list of clauses instead,
	with one element of the disjunction as each new clause's head:
	0.5::reallycold; 0.5::freezing <--- [cold]
	↓
	[0.5::reallycold <--- [cold], 0.5::freezing <--- [cold]]
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
	transformed:assertz(Transformed).
assert_clause(_Weight::Head <--- [BodyHead | BodyRest], Weights, DisjunctionIndex, HeadIndex) :-
	Body = [BodyHead | BodyRest],
	maplist(term_variables, Body, ConjunctionsVariables),
	flatten(ConjunctionsVariables, Variables),
	list_to_conjunction(Body, BodyConjunction),
	Transformed = (Head :- (BodyConjunction, sampler:sample_head(Weights, DisjunctionIndex, Variables, NH), NH = HeadIndex)),
	generate_clause_samp(Weights, DisjunctionIndex, Variables, Generated),
	transformed:assertz(Transformed),
	transformed:assertz(Generated).


generate_clause_samp(Weights, DisjunctionIndex, Variables, Samp) :-
	Samp = (samp(DisjunctionIndex, Variables, Val) :- (sampler:sample_head(Weights, DisjunctionIndex, Variables, Val)) )  .

/*
	Transform a list of terms extracted from an object program's clause
	into a standard prolog conjunction.
*/
list_to_conjunction([Term], Term) :-
	!.
list_to_conjunction([Term | Rest], ','(Term, Conjunction)) :-
	list_to_conjunction(Rest, Conjunction).

/*
	Cleanup environment state (usually after running a sampling process to completion).
 */
unload_program :-
	findall(Predicate, current_predicate(transformed:Predicate), Predicates),
	maplist(transformed:abolish, Predicates).

/*
	Generate a sample for a head, given its respective weights.
*/
sample_head(_Weights, RequiredHead, Variables, HeadId) :-
	recorded(samples, (RequiredHead, Variables, HeadId), _), !.

sample_head(Weights, RequiredHead, Variables, HeadId) :-
	sample(Weights, HeadId),
	recorda(samples, (RequiredHead, Variables, HeadId), _).

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

/*
	Assuming a suitable object program has already been transformed via [load_program],
	take a sample of the given [Goal].
*/
sample_goal(Goal) :-
	abolish_all_tables,
	clear_recorded_pl_heads,
	transformed:call(Goal).

/*
	TODO: Gibbs sampling requires sample_head to use assert instead of recorda/recorded.
	Read: https://ceur-ws.org/Vol-2678/paper12.pdf or https://link.springer.com/chapter/10.1007/978-3-030-35166-3_2
		  for further information regarding sampling (Gibbs/ MCMC-sampling).
		  
	TODO: Offer interface predicate to sample a goal given certain evidence (see link #1).
*/
sample_goal_gibbs(Query) :-
	Block is 2,
	remove_samples(Block, Removed),
	copy_term(Query, Query1),
	transformed:call(Query1),
	ensure_sampled(Removed).

remove_samples(Block, Samp) :- remove_samp(Block, Samp); Samp = [].

remove_samp(0, []) :- !.
remove_samp(Block, [(RequiredHead, Variables) | Samp]) :-
	recorded(samples, (RequiredHead, Variables, _), DbReference),
	erase(DbReference),!,
	RemainingBlock is Block - 1,
	remove_samp(RemainingBlock, Samp).

ensure_sampled(S) :- maplist(check_sam, S).

check_sam((RequiredHead, Variables)) :- transformed:samp(RequiredHead, Variables, _).

/*
	Erase all previously recorded sample entries from the database.
*/
clear_recorded_pl_heads :-
	findall(DbReference, recorded(samples, _, DbReference), References),
	erase_all_references(References).

erase_all_references([]).
erase_all_references([Reference | Rest]) :-
	erase(Reference), erase_all_references(Rest).
