# Additional searches below 194 states

No sub-194 machine was certified. The accepted PA194N6 construction is
independent of every unsuccessful search in this directory.

## New fixed-word grammar searches

`global_parse.cpp` reparses the complete 190-token AX word using a dynamic
program over its distinct substrings and randomized repetition weights.
`window_parse.cpp` instead reparses one whole subtree against the current
shared-subtree dictionary. These are larger moves than one tree rotation.
Both retain the supplied exact simultaneous-history-fold scorer and its
scanner-shape penalties. They preserve the macro word, but a favorable score
would still require source-graph comparison, literal physical checks, and
exact blank initialization.

The completed 180-second runs recorded respectively 3,278 and 1,113,967
proposal slots. Both retained best effective reader count 60, which adds to
the fixed 134 controls to give 194. The second run accepted 733,412 slots.
Slots include duplicates, unchanged candidates, and skipped proposals; they
do not count distinct verified machines. CPU time bounds are hardware
dependent, so the exact proposal counts are not reproducibility targets.

`min_grammar.py` is a separate mixed-integer model of a fixed-word dictionary.
It considers every repeated substring (226, including the two free increment
macros), together with the full word. Each selected production is a path
through a token-position flow graph; the objective is the sum of RHS length
minus one, treating the inherited two- and four-increment macros as free.
The 180-second HiGHS run found feasible cost 67 and reported bound 63. It
did not establish optimality. This is a grammar cost model, not the physical
machine state objective, and the numerical solver output is not a formally
checked lower-bound certificate. `bin_grammar.cpp` tried 1,220,188 random
binarizations of its returned production skeleton for 60 seconds. Its best
penalized score was 69; this does not provide a new accepted machine.

The C++ scorer and original tree infrastructure are copied from the pinned
ProveIt PA194 packet. Its notices are retained in `licenses/`. The three
reparsing drivers and the MILP experiment are new to this package.

Example replay commands (from this directory):

```sh
c++ -O3 -std=c++17 global_parse.cpp -o global_parse
./global_parse inputs/seed194.txt inputs/leaf_attrs.txt replay_global 180 2026111408
c++ -O3 -std=c++17 window_parse.cpp -o window_parse
./window_parse inputs/seed194.txt inputs/leaf_attrs.txt replay_window 180 2026111409
python3 min_grammar.py
c++ -O3 -std=c++17 bin_grammar.cpp -o bin_grammar
./bin_grammar inputs/seed194.txt inputs/leaf_attrs.txt min_productions.txt replay_bin 60 2026111410
```

The MILP script requires NumPy and SciPy with `scipy.optimize.milp`. The
other scripts use Python's standard library and a C++17 compiler.

## New local searches on PA194N6

The native table is frozen at SHA-256
`63b6f604ee34ee119eb92ce3125021257204142854dec416c6b955f0560b975a`.
The context collector checks all 4,877 source outcomes, observes unary
sweep interiors and the four generic-list proofs, and includes the complete
58,320-step blank initialization. It records 19,318 symbolic local views
covering every one of the 194 controls, expanded conservatively to 29,282
eleven-cell windows (radius five).

The inherited common-action state merger and per-incoming-edge bypass
operator both returned zero candidates with a 300-step local bound. Their
complete source, frozen windows, and new logs are included. The former
identifies two controls with one surviving control; the latter gives every
incoming edge its own replacement action when removing a non-self-looping
control. Neither rule covers arbitrary machine transformations.

Re-run the two complete local screens, checking their actual empty results:

```sh
python3 replay_physical.py
```

Use `python3 replay_physical.py --collect` also to regenerate the symbolic
contexts before screening. That mode normally takes several minutes. New
outputs are created in a temporary directory and do not overwrite the
recorded evidence. The symbolic collector is an inherited executable
verification component, not a proof-assistant kernel.

All counts and precise scopes are in `summary.json`. No negative result
here is a lower bound on arbitrary PA-consistency Turing machines.
