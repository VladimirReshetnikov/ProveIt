# Tagged register transport: compact negative search replay

This folder contains the literal inputs and bounded search used to test
coordinated register renamings together with the initialized218-state fold.
It contains no claimed blank-start218 machine.

Run `python3 -B reproduce.py --output replay` with Python3 and a C++17 compiler
available as `g++`. The full replay performs28 searches and verifies the
recorded integer counts. `--limit 1` runs a clearly marked partial smoke check.
The input and C++ source bytes are pinned in `reference.json`.

The generator preserves indirect/tagged leaf entries, transports their direct
selector rows, and deletes301 by the88/51 fold only when the required shared
row equalities hold. All362,880 register permutations are considered for each
input;120,960 pass the stated row constraints. There is no compiler-correctness
claim for this whole family: the result is a literal startup obstruction for
these exact generated tables.

The recorded searches cover3,386,880 table/start configurations. Each run
enters either a self-loop moving into the infinite blank exterior or an exact
repeated finite configuration modulo translation, with all one-cells retained
in the comparison. There are no still-bounded, tape-limit, or seed-hit outcomes.

For the two original source layouts, all possible designated start states are
covered by eight first-write representatives. Before the first1 is written,
the tape remains blank. The run either repeats an allzero state, halts, or
reaches one of the only eight read0 rows that write1:0,4,16,35,66,74,97,198.
Reaching such a state on a blank tape is the same starting configuration up to
translation. State35 is immediately a blank-ray loop; the other seven are
explicitly screened. The generated selector changes preserve this eight-state
set. The additional14 phase/layout inputs are screened from start0 only.

The clean-frame predicate permits arbitrary natural nextproof, additive
parameter, and proof-list values at the correctly permuted physical columns,
requires all other primary values zero, and permits any nonempty finite list
of natural spare values. A clean frame must include the complete represented
tape and zero exterior. General clean-seed calibration is explained separately
in `source218/general_seed_lemma.tex` in the research tree.
