PA194 discovery record
=====================

The final machine does not require rerunning a stochastic search. Its grammar,
folds, source graph, literal tables, local proofs, runtime contracts, and startup
are checked deterministically by ../pa194/build_verify.py.

Bind the saved search witness to the delivered grammar:

    python3 -B reconstruct_grammar.py

The successful association search is included as optional discovery material.
It starts from a separately verified 195-state implementation of the same
190-token emitter. The source word, formula parameters, and axiom order are fixed.
It explores shared-subtree and single-occurrence rotations, scores allocated
reader nodes and compatible local history folds, and checks simultaneous local
fold compatibility for competitive grammars.

On this recorded run, seed 419792651 reached the selected shape at cycle 2081,
iteration 2218, zero-based, after exactly 6,245,219 iteration slots. An iteration
slot need not produce a legal rotation. This count is not a count of every
internal score evaluation. The chosen shape has 68 AX readers and 8 compatible
folds, predicting 134 + 68 - 8 = 194. Complete machine validation followed separately.

Optional replay, using a C++17 compiler, from this directory:

    g++ -O3 -std=c++17 association_search.cpp -o /tmp/pa194_association_search
    /tmp/pa194_association_search separate_input.txt 2082 419792651 fixed

The search writes parameter_best.json and parameter_candidate.json together
with their .shape and .word files into its current working directory. The frozen
accepted witness is retained under winner.*. A successful search score alone
is not a correctness proof, and the search does not establish any lower bound.

Inputs and original source semantics ultimately come from the PA195 package
and James Chang's PA196 development as cited in the main article. The source
and licenses of the inherited compiler and symbolic runtime are preserved in
../reference/pa195_conpa/pa195/vendor/.

search_ledger.json records the other bounded search families. Interrupted runs
are counted only through their last fully logged cycle; unlogged tails are
excluded. Sources, static inputs, and logs are retained under exploratory/.
No unsuccessful search is a proof of a state-count lower bound.
