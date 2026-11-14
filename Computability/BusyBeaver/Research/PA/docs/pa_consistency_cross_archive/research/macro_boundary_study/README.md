# Whole-instruction state-fold screens for PA196

## Result and scope

No sub-196 consistency machine is established by this study. The included
196-state table is the unmodified James Chang baseline, not a new candidate.
The completed screens and their exact counts are recorded in `receipt.json`.

The experiment changes the simulation boundary. Earlier repository screens
require one parent TM step to match a short child block. Here a candidate is
allowed to redistribute work over an entire source instruction, provided it
reaches the required full-tape endpoint. This is a genuinely different finite
search condition, but it is still a bounded filter rather than an unbounded
verification theorem.

The source is frozen at ProveIt commit
`906367250a7f96c923147b10df392294bced7be5`. The inputs are the table and
`PA196/Program.lean` under
`Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/`.
The table has SHA-256
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.

## Tests

`build_inputs.py` parses the explicit 159-internal-node source tree and obtains
3,812 instruction occurrences. Two source resolvers, one using binary
addresses and one using ancestor intervals, agree on every successor.

The unguarded fixture has 4,959 cases: every source instruction and both
branches of each decrement. All nine primary registers are zero except that
the decremented register is one in the positive case. The frame has gap 48
and one spare register with value zero. Each case specifies the entire
finite-support input and expected output tape, head, and control. Increment
appends a spare of value one; positive decrement increases the gap by one.
Every baseline case is executed literally and checked against this endpoint.
A greedy 59-case prefix covers all 392 baseline transition rows.

The guarded fixture first computes the least zero/positive-mask
overapproximation from source site 25 and register vector
`[2,0,0,0,0,0,0,0,0]`. It contains 274,880 site/mask pairs at 3,810 sites.
Initial inclusion and closure are audited separately after discovery. For
each admitted source branch the fixture selects a mask of minimum number of
positive registers, breaking ties numerically, and instantiates positive
registers by one. There are 4,956 cases; these still exercise all 392 rows.
These masks are an overapproximation, not a claim that the selected concrete
frames occur in the blank run.

## Candidate family

Delete a working state `a`, retain another working state `b`, redirect all
targets of `a` to `b`, and replace one retained transition row by an arbitrary
legal write bit, direction, and retained-or-halt target. The usual screen
places the modified row at `b`; the helper extension allows any retained row.
No state label is identified with the halt label.

For a chosen deleted state there are 195 keepers, two retained-row choices,
and 784 actions per row, hence 305,760 assignments. Counts are assignments,
not necessarily distinct transition tables. The 49-state engine/router set
is reproduced from the repository's `protected-core.txt`; the complementary
147 labels are in `decoder_drops.txt`.

The helper extension intersects the sets of rows visited by the unpatched
fold on failed tests. Every one-row repair meeting the same execution budget
must modify a visited row in each such failure. Candidate rows in that
intersection are then enumerated and checked. Only the ten completed deleted
states in `helper_prefix_drops.txt` are claimed in its recorded result.
The longer run was stopped during deleted state 14; no partial count from
that unfinished state is included.

## Three endpoint conditions and rejection reasons

The unguarded and guarded exact screens require the projected root control,
the original head position, and equality of the entire 256-cell tape array.
The tape outside that array is initially blank; leaving the array is a
failure of this finite test, so no outside write is silently discarded.

The relaxed engine screen uses guarded fixtures and permits a different gap
of at least 48 and any nonempty finite list of valid spare register blocks.
It still requires the same left marker, source address, head, root control,
and all nine primary values. The input fixtures remain finite samples; this
does not quantify over arbitrary register values or spare lists.

All screens execute at most `max(800, 2 * parent_steps + 64)` child steps per
case. They reject separately in the implementation when the candidate halts
unexpectedly, leaves the finite tape window, or exhausts that budget without
the required endpoint. Visiting a different root configuration does not
immediately reject a candidate; later convergence within the budget is
allowed. Search logs record cumulative counts, not a histogram of these
three rejection categories. The independent controls record their individual
rejection reasons in `macro_controls.json`.

Consequently, “zero survivors” means that no tested assignment passes this
endpoint screen. It does not prove a global lower bound, different halting
behavior on blank input, or the impossibility of a longer macro simulation.
Even a survivor would need arbitrary-value contracts, blank startup,
unbounded trace extraction, and the PA-internal consistency biconditional.

## Controls

`macro_controls.py` is a separate naive set-of-cells simulator. It confirms
all 4,959 baseline endpoints and all 4,959 endpoints after inserting a real
two-step head round trip before every root/read-zero action. The latter
control shows that the endpoint test admits stuttering. A deliberate immediate
halt is rejected as an unexpected halt; a deliberate infinite rightward
motion is rejected upon leaving the finite window. These controls are finite
checks, not a formal proof of the search implementation.

## Reproduction

Python 3.10+ and a C++17 compiler suffice. Run from this directory:

```sh
python3 build_inputs.py
python3 macro_search_gen.py
python3 macro_guarded_gen.py
python3 macro_controls.py
g++ -O3 -std=c++17 macro_folds.cpp -o macro_folds
g++ -O3 -std=c++17 macro_helpers.cpp -o macro_helpers
g++ -O3 -std=c++17 macro_loose.cpp -o macro_loose
./macro_folds upstream/data/pa196.tm macro_tests.txt drops.txt
./macro_folds upstream/data/pa196.tm macro_tests.txt decoder_drops.txt
./macro_folds upstream/data/pa196.tm macro_guarded_tests.txt drops.txt
./macro_loose upstream/data/pa196.tm macro_guarded_tests.txt drops.txt
./macro_helpers upstream/data/pa196.tm macro_tests.txt helper_prefix_drops.txt
```

The helper search is more expensive than the keeper-row screens. Reproduction
should compare assignments, deleted-state coverage, and survivors; elapsed
seconds and incidental run-call counts are not scientific conclusions.

## Provenance

James Chang's input table and Lean source retain the upstream MIT license.
The small source resolver and unary-register helpers are the repository's
retained adaptations of the K/U verification tools; their source comments and
ProveIt/Wade notices are preserved. New files in this directory implement only
the finite searches and their controls. No claim of a new formal PA theorem
is made.
