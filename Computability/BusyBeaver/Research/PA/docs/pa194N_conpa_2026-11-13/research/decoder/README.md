# Expanded decoder and contextual-fold searches

These five completed, time-limited heuristic runs screened 25,215,463 proposal
slots. No score below 194 working states was found. Proposal slots can repeat
the same grammar; this number is neither a count of distinct machines nor an
exhaustive search bound. The accepted PA194N theorem does not depend on these
discovery searches.

The count used by the screen is 134 fixed controls plus the effective reader
allocation score. All runs reached a best score of 60, giving 194 states.
`summary.json` records the exact budgets, seeds, totals, and log hashes.

The inputs expose the interiors of pure reader macros, preserving the exact
source order. The first run uses AX-reader folds. The `general` run also
allows compatible folds with fixed reader endpoints; `general_prune` adds
a heuristic restriction requiring partially selected fold sets to remain
valid. The `nopush` run changes the fixed controller to PA194N. The `deep`
run opens deeper push, cons, and guard interiors. Previously supplied work
already used ABC-tail expansion and free fixed pairs; no priority for those
ideas is claimed.

## Replay

Use a C++17 compiler, from this directory. The frozen inputs suffice; no
checkout or network is needed. Time-limited runs can perform different
numbers of proposals on different hardware, even with the same random seed.

```sh
mkdir -p replay
c++ -O3 -std=c++17 macro_expand.cpp -o replay/expanded
c++ -O3 -std=c++17 macro_general.cpp -o replay/general
c++ -O3 -std=c++17 macro_general_prune.cpp -o replay/general_prune
c++ -O3 -std=c++17 macro_nopush.cpp -o replay/nopush
c++ -O3 -std=c++17 deep/macro_nopush_deep.cpp -o replay/deep
replay/expanded seeds.txt leaf_attrs.txt replay/expanded 600 202611132101
replay/general seeds.txt leaf_attrs.txt replay/general 600 202611132103
replay/general_prune seeds.txt leaf_attrs.txt replay/general_prune 600 202611132104
replay/nopush seeds_nopush.txt leaf_attrs.txt replay/nopush 700 202611132113
replay/deep deep/seeds_nopush.txt deep/leaf_attrs.txt replay/deep 700 202611132114
```

The companion `screen*.cpp` files implement the corresponding allocation
models and are included by the search drivers. Keep their relative paths.
The `.seed*.grammar.json` files record final pools, not newly certified
machines. CSV files and logs retain the completed runs.

## Regenerate the input expansion

`prepare_inputs.py` reads the pinned repository snapshot named in the root
README. For example:

```sh
python3 -B prepare_inputs.py --repo /path/to/ProveIt --output /new/inputs --depth 1 --controller original
python3 -B prepare_inputs.py --repo /path/to/ProveIt --output /new/nopush_inputs --depth 1 --controller nopush
python3 -B prepare_inputs.py --repo /path/to/ProveIt --output /new/deep_inputs --depth 2 --controller nopush
```

Each invocation writes `seeds.txt`, `leaf_attrs.txt`, and `source_map.json`.
The archived no-push seed files were renamed `seeds_nopush.txt` for clarity.
Every promising scored grammar would still require exact source equivalence,
validation of all simultaneous folds, and the complete physical contracts.
None of these negative runs establishes a state lower bound.

The C++ search code derives from the supplied PA decoder-search material.
Upstream notices are retained in `../../licenses/`; the exact upstream
repository and commit are recorded in `../../PROVENANCE.json`.
