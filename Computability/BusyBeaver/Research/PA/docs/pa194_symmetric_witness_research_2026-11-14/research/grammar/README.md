# Further symmetric-witness grammar searches

Two new five-minute stochastic searches attempted to save another reader
state after applying the new symmetric cache transformation. Neither found
a sub-194 candidate. Exact counts, random seeds, and final logs are in
`receipt.json`, `H5XS_run.log`, and `JH5XS_run.log`.

The search uses subtree reassociation, including shared-subtree and
individual-occurrence rotations, preserving the flattened macro word.
The parameter-permutation routine inherited in the source is not invoked
in these runs. Macro order, numerical calculus, scratch discipline and
command semantics remain fixed. Heuristic penalties constrain parser
shape, including height and path bounds; these further restrict the search.
Trial counts are not counts of distinct grammars.

The inputs preapply the fixed-control fold 41→330, leaving 134 fixed
controls. For candidate generation, compatible reader folds are checked
simultaneously by the inherited local-context screen. Effective reader
count 60 means 194 total states; a candidate with at most 59 effective
readers would still require complete source, literal tape and blank-start
verification. No such hit occurred.

## Replay

Build with any C++17 compiler and run from this directory:

```sh
c++ -O3 -std=c++17 search.cpp -o /tmp/pa194-grammar-search
/tmp/pa194-grammar-search PA194H5XS.templates.txt leaf_attrs.txt /tmp/H5XS 300 15110201
/tmp/pa194-grammar-search PA194JH5XS.templates.txt leaf_attrs.txt /tmp/JH5XS 300 15110202
```

These use a wall-time limit. Exact trial counts and final retained pool
depend on hardware, compiler, and elapsed time; random seeds reproduce
the stochastic sequence under the same implementation. The frozen logs
record the actual completed runs. Neither the candidate screen nor absence
of a hit proves a state lower bound.

The `*.templates.txt` files freeze each new raw fixed controller with
41→330 applied and the corresponding compressed source tree. They contain
the complete inputs required by the search; the final new machine itself
is reconstructed independently by `../../construction/build_symmetric.py`.

## Attribution

`screen.cpp`, `leaf_attrs.txt` and `search.cpp` are based on the retained
witness packet's `research/grammar/screen.cpp`,
`research/grammar/leaf_attrs.txt` and `research/grammar/search_h5X.cpp`. The small
local addition saves the initial grammar for the audit. See the root
`WITNESS_NOTICE.md` and `references/pa194_witness_research_2026-11-15.zip`.
The new search inputs are the two symmetric implementations in this work.
