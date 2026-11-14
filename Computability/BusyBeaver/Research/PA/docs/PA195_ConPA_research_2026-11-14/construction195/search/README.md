# Optional discovery search

The construction is fully specified by `../grammar.json` and `../folds.json`.
The search is optional. Rebuilding and checking the machine requires only
`python3 ../build_check.py`; finding it again is unnecessary.

This directory preserves the standalone C++ search that found the selected
grammar, its numeric inputs, and its observed receipts. It uses only the
C++17 standard library:

```sh
g++ -O3 -std=c++17 search_exact.cpp -o search_exact
./search_exact templates.txt leaf_attrs.txt retry 240 140216
```

The fourth argument is a wall-clock time limit in seconds and the last is
the random seed. The inputs contain all 134 fixed rows and 101 initial tree
shapes; they do not access a repository checkout or network resource. A
different computer may complete a different number of proposals within the
same wall-clock limit. Search output is a candidate generator, and every
candidate still requires the full Python certificate checks.

The search explores global replacements of shared binary subtrees by their
two elementary reassociations, together with independent permutations of
the three local parameters in each of the six unrestricted AX heads. Its
fitness counts distinct reader nodes minus mutually compatible contextual
folds, with penalties for scanner and entry-side constraints. Near the target
it exhaustively checks all helper alternatives and validates all selected
folds simultaneously on the final local transition table. The penalty and
the fold fitness are preliminary filters; the complete symbolic contracts
and blank initialization are the acceptance tests.

The recorded run used seed 140216, made 4,039,217 proposals in 240
seconds, accepted 713,374 search moves, and saved 30 target-score hits.
There were 28 distinct saved grammar trees. All 28 passed the full 195C
symbolic and startup checks, as recorded in `candidate_checks.json`.
`discovery.log` and `discovery.csv` preserve the observed run, including the
first score-61 hit at proposal 3,472,170. The selected frozen grammar is
`../grammar.json`, corresponding to `exact.best.grammar.json` in the log.

Every recorded successful hit used the identity parameter permutations
`000000`. The selected solution therefore preserves both the AX word and
the order of all heads. Independent permutations enlarged the search space
but are not needed for the final mathematical construction.

The local exact fitness was cross-checked against the independent Python
fold solver on 245 baseline and previously found tree shapes;
`cpp_python_controls.json` records agreement on all cases. An earlier
fixed-shape scan of 101 shapes times all 46,656 local parameter assignments
found no score below 62. An earlier optimistic-matching search produced
144 distinct apparent score-61 shapes, but simultaneous Python checking
gave 196 or 197 states for every one. These observations explain why exact
compatibility, rather than a maximum-matching estimate alone, was essential
to selecting a valid candidate. They are bounded-search observations, not
a lower-bound theorem.

`screen.cpp` is shared support for the annealer and can also run the finite
parameter scan. The included version contains a defensive missing-state
check in its local simulator. The final table certificate is checked by
Python independently of this search implementation.
