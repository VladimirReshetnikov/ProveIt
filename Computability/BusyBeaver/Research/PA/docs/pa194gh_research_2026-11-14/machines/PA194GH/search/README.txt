GH source compression search
============================

New run using GH's actual fixed rows and G's accepted explicit-binder
source as the initial word/grammar. It adapts the supplied PA194G search;
new frozen inputs are in inputs_four.hpp.

Seed: 202611140377
Main stochastic iteration slots: 3,000,000
Scored evaluations: 2,633,281 (including seed/restart/repair evaluations)
Skipped non-reassociable proposals: 368,507
Accepted proposals: 1,420,200
Best optimistic effective reader score: 60
Fixed state term: 134
Best projected total: 194
Four gate-family minima: 60,67,65,66

Permutations of the seven unconditional axiom heads, parameter-role
assignments, selected premise exchange and equality orientation, four gate
associations, and repeated binary-tree rotations are explored. The score
uses a maximum matching of syntactic contextual-helper candidates. It
ignores possible conflicts between simultaneous helper substitutions.
Therefore a low score is only a lead; the delivered machines were built
and validated separately with explicit compatible folds.

This stochastic search is not exhaustive and proves no state-count lower
bound. No projected score below194 occurred in this run. The exact all-
control pair-matching searches on the frozen raw GH/GHS tables are in
matching_search.json next to their respective tables.

Reproduce:
    g++ -O3 -std=c++17 source_search.cpp -o search_gh
    ./search_gh 3000000 202611140377 replay

The root package does not require a C++ compiler for its delivered-table
and mathematical-command verifications. The search executable is not
shipped. The final witness grammars and progress/summary records accompany
the source.
