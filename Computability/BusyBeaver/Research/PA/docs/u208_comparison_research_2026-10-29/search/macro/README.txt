Extended macro alias search (new this iteration)
===============================================
macros.cpp tests deleting q and redirecting all incoming targets to r, with
no other transition edits. It does NOT force an old one-step endpoint.
Instead old q and new r runs share an initially arbitrary symbolic tape,
and it compares every positive old/new prefix pair for common state/head/
complete tape, excluding deleted q. Both runs can write temporarily and later
restore cells. Halt endpoints can agree without final head/tape equality.
Symbolic initial cells are split into both bits when first read, shared by
both executions. Every branch must find a match within the bounds.

Guard coverage uses the previous self-authored complete finite backwards
history enumerator; all feasible suffix contexts are included, with shorter
prefixes from initialstate0. q0 is never deleted. A context overapproximation
can make the search miss a reduction but cannot justify a false positive.
Every accepted candidate would still need an independent proof/checker and
full runtime audit. No candidate was accepted in the actual U208 searches.

Finite bounds:8or12 backwardedges, atmost16/32(and64followon)steps per side,
headradius30,3000DFS nodes percontext. All42849 distinctordered(q,r) with
q!=0, r!=q were tested for each input class. Rejection at a resource bound
is inconclusive. The result is NOT a lowerbound or exhaustive algorithmic
minimality claim.

Inputs8edge from ../..table_search/{89145587,4564c487}.dat;12edge regenerated
by export12.py using priorownedtable_search/core.py. Tables refer to our
Plain8edb41dc andCompatibilitybdf724e5 U208 variants, which represent all
current incoming graphs by comparison.json.

positive_control.dat is a tiny five-state fixture. q1->r2 is accepted at
matching two-step endpoints while a one-old-step endpoint matcher cannot
accept it: old enters3, which r2's looping path never visits. This checks
that the new search genuinely exceeds the earlier direct alias criterion.
Compile with g++ -O3 -std=c++17 macros.cpp -o macros.
Run ./macros INPUT.dat STEPBOUND; output includes trials, hits, nodes, time.
