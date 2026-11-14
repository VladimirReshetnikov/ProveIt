# Bounded search record

These searches did not establish a machine below 194 states. The authoritative
construction is outside this directory, at `../construction/output/pa194C.tm`.
The searches are optional discovery work and are not required for its proof.
They establish no global state lower bound.

## Grammar searches

The C++17 searches are adaptations of the primary PA194 packet's
`search_plateau.cpp` and `screen.cpp`, with both accepted 194-state grammars
as seeds. `search_occurrence.cpp` includes both all-occurrence and individual
occurrence rotations. `search_expanded.cpp` exposes copying macros as push
followed by additive copying. `search_closure.cpp` exposes further closed
subblocks and recognizes existing fixed reader pairs.

The corrected closure generator keeps distinct source-token identities even
when the physical controls coincide. Physical aliases are context dependent;
therefore a good allocation score is only a candidate. `validate_closure.py`
checks the complete primitive word and resolved source graph, two independent
source resolvers, compatible folds, complete startup, and every symbolic
runtime contract. The smoke seed reproduces primary PA194 byte for byte.

Example replay, from this directory:

```sh
g++ -O3 -std=c++17 grammar/search_occurrence.cpp -o /tmp/pa-occurrence
/tmp/pa-occurrence grammar/seeds194.txt grammar/leaf_attrs.txt /tmp/pa-occurrence 900 202611131933

g++ -O3 -std=c++17 grammar/search_expanded.cpp -o /tmp/pa-expanded
/tmp/pa-expanded grammar/expanded_seeds.txt grammar/expanded_attrs.txt /tmp/pa-expanded 900 202611131945

g++ -O3 -std=c++17 grammar/search_closure.cpp -o /tmp/pa-closure
/tmp/pa-closure grammar/closure_seeds.txt grammar/closure_attrs.txt /tmp/pa-closure 900 202611141946
```

Runtime is time-bounded, so iteration counts need not reproduce exactly on a
different computer. Seeds, inputs, sources, and complete observed run logs are
included. The initial erroneous closure log is retained only for audit and is
explicitly excluded from accepted search results; its aliasing issue is recorded
in `physical/research_summary.json`.

Validate the published closure smoke grammar (not a new machine):

```sh
python3 -B physical/validate_closure.py physical/closure_smoke.seed0.grammar.json --target 194 --output /tmp/pa-smoke
```

## Local physical searches

The C++ programs inspect finite windows and bounded detours. Their generic
invocation is `PROGRAM NATIVE_TABLE RADIUS STEP_BOUND [CONTEXT_FILE]`.
Use the native labels, whose start is 74. The supplied context files refine
conservative all-tape windows using symbolic source contracts. They are not
claims that all finite machine behavior has been exhaustively searched.

For example, from this directory:

```sh
g++ -O3 -std=c++17 physical/action_merge_boxes.cpp -o /tmp/pa-local
/tmp/pa-local reference/pa194/construction/tables/pa194.native.tm 4 100 physical/generated/literal_patterns_k4.txt

g++ -O3 -std=c++17 physical/eliminate.cpp -o /tmp/pa-eliminate
/tmp/pa-eliminate reference/pa194/construction/tables/pa194.native.tm 6 200 physical/generated/symbolic_patterns_k6.txt
```

`action_merge_future.cpp` permits an exact join with a bounded future original
configuration. `eliminate.cpp` searches for removal of one control by rewriting
all its incoming transitions. `literal_contexts.py` derives arithmetic-list
contexts using the independent whole-tape engine. The register-permutation
script is a separate finite randomized experiment; its interrupted tail is not
counted as an exact completed result.

`physical/sat_triples.py` and `sat_triples_near.py` additionally use Z3
(tested with z3-solver 5.4.1) to synthesize two survivors of a three-reader gadget.
Their recorded queries timed out: they produced neither a verified candidate
nor an unsatisfiability exclusion. They are explicitly inconclusive and are
not part of the standard-library verification suite.

`PORTABILITY.json` records the reference-path-only adaptations made to Python
research scripts for this package layout. C++ numerical inputs and run logs
retain their observed contents. The copied parent sources preserve their
original notices and attribution.
