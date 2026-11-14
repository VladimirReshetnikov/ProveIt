# ZFC / ConciseIPRA transfer study and additional PA state searches

Snapshot: `VladimirReshetnikov/ProveIt` commit
`75a42a28ca818627f5a104fb0f0c7f7d02a52947`.

## Outcome and scope

This investigation did **not** produce a certified binary, one-tape, blank-start PA consistency machine below 194 working states. The included programs and receipts are additional searches and negative screens. A low heuristic score, a bounded physical simulation, or a short checker in another language is not a consistency calibration.

## What transfers from the other projects

The ZFC K215 project separates source transformations, numerical-calculus calibration, physical state allocation, complete quantified runtime verification, and exact blank initialization. Its useful engineering techniques include command permutation, source reassociation, partial selectors, sharing through a preceding history bit, and checking local contextual entries rather than demanding one global physical representative for every source node. K215's README binds its own 215-state binary machine and describes compiled Lean and Rocq endpoint proofs. Those theorems are about ZFC and that exact machine; they are not PA endpoints for a modified table.

The PA frontier already uses major logical ideas developed in the ZFC work, notably a dominated implication axiom and diagonal vacuity. They cannot be counted as fresh savings merely by applying the same names again. This investigation tested further sharing and source reassociation instead.

ConciseIPRA measures complete standalone Python checker size after normalization, with token, AST-node, and byte coordinates. Its native scalar calculus is calibrated to first-order intuitionistic primitive recursive arithmetic. Its progress induction rule is restricted to literal equations. The numerous smaller rule presentations are proved equivalent to that same kernel. Replacing a PA refutation enumerator by one of these checkers would therefore need a new PA-strength calibration, in addition to an explicit binary TM compilation. A natural research direction is to replace equation induction by full-formula induction and prove the resulting calculus equivalent to an intuitionistic arithmetic presentation equiconsistent with PA. That extension and its state cost were not established here.

Primary repository references:

- `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md`
- `Computability/BusyBeaver/Research/PA/README.md`
- `Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/report/calibration.tex`
- `Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/reference/diagonal_calculus.tex`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`

## Additional searches

### One new direct selector

A selector has rows `0 -> 0 R u` and `1 -> 1 R v`. A pair of source controls can sometimes share one physical control by moving left to this selector, using the preceding history bit, and returning to the current cell. The experiments enumerated useful direct selectors and checked whether the possible simultaneous folds repay the extra state.

1. `one_helper_screens/194_results.json` records a screen of all 49 state-renaming classes with 194 working states in the repository's `MACHINES.tsv`. No single new direct selector enabled two disjoint additional folds in the tested family. This family protects the selector target controls and uses the one new selector for every differing read branch. Its negative result is not a general lower bound.
2. `one_helper_screens/195_202_results.json` records 168 retained table representatives with 195–202 states, excluding `/comparison/` and `/census/` copies. The broader screen permits existing selectors together with one new selector and uses an exact two-cell simultaneous trace checker whenever the matching bound reaches the requested target. No candidate reached 193 states. The raw primary 201-state source changes from matching bound 7 to at most 8 with one helper, so the extra state cancels the extra fold.

The stronger exact rational LP obstruction produced by the other research branch supersedes this last primary-table observation: it handles arbitrarily many selectors within its explicitly specified frozen-grammar family. It is not part of this directory.

The Python screening scripts record absolute checkout paths as used during the run. To rerun against another checkout, change `ROOT` to the pinned checkout path. The supplied `MACHINES.tsv` in that checkout determines the complete tested set. The JSON records retain the exact source table paths and table classes.

### Repeating already available theorem heads

The source can safely emit another copy of an already emitted theorem head, or an extra zero/truth entry, without strengthening the represented calculus. The experiment inserted one of seven heads or truth at eight head boundaries, then considered multiple insertion associations and searched the resulting binary source trees. In the stronger 192-seed run, 2,801,896 proposals in 240 seconds achieved effective reader score 61, corresponding to 134 fixed states + 61 = 195 states. No 193-state hit was found. These are search scores; no additional claimed machine is certified by that run.

`redundant_head_search/` contains its exact C++ program, input templates, macro attributes, and log. Compile and run from that directory:

```sh
g++ -O3 -std=c++17 search.cpp -o search
./search input.txt leaf_attrs.txt rerun 240 2026111402
```

The original seed is recorded in the log; a different random seed or timing can change the heuristic trajectory. The textual source inputs are the complete fixed-row and source-tree search instances.

### Removing the six-zero scanner state and exposing a shared helper

This combines the root/MP source rotations supplied by the parent research branch with an explicit AX macro expansion. The fixed part has 133 controls after deleting scanner state 34 and changing state 23's zero branch to state 75. It includes the root rotation through states 84/310/53 and the MP rotation through states 100/174.

State 69's zero transition now requires a swapped selector: history zero must select the old node20 continuation, while history one selects node72. The source expansion at macro positions 8–9 is

`cons, node75` -> `cons, node74, cons`.

Here `node75 = (node74, cons)`. A source subtree `(cons, node74)` provides the desired selector `(90,92)` without adding a separate fixed helper. The search requires that subtree and patches row `69/0` to `0 L <that reader>`. It treats `(92,90)` as the already available state 213 and permits node72 only as a right child. The new macro word has 191 tokens. Head parameter-permutation boundaries were shifted by one beyond the inserted token; no prefix instruction is treated as a parameter.

The scanner bound is maximum zero-run five and maximum pre-increment zero-run four. These are synthesis filters; every candidate would still need the complete resolved source graph, quantified runtime, and exact blank-start checks. None passed the score threshold for that final validation. The included best grammar has a nonzero scanner penalty and is **not a valid shortened-scanner machine**.

`source_search/search.cpp`, `screen_global.cpp`, `input.txt`, and `leaf_attrs.txt` are the exact final search instance. To reproduce:

```sh
g++ -O3 -std=c++17 search.cpp -o search
./search input.txt leaf_attrs.txt rerun 300 221347
```

The search's score is the reader count minus a fold bound, plus any synthesized helper cost, plus context/scanner penalties. It checks simultaneous local compatibility when a penalty-free score could reach the target. A score at most 60 with zero penalty is necessary for 133 + 60 = 193 physical controls. There was no such hit. Time-limited annealing is not an exhaustive proof of impossibility.

Finally, `source_search/swapped_window_screen.py` tries every existing fixed control, both writes, and both move directions as a replacement for row69's zero transition, on every binary neighborhood of radii 1 through 4. It requires the correct history-dependent target and exact restoration of the neighborhood within 150 transitions. There are no hits. This is an exact finite screen of those bounded local templates, not a theorem excluding longer or different simulations.

## Provenance and proof status

The source annealers derive from the repository's PA194 source rebracketing and folding search programs. New work here is the particular source-variant generation, direct-selector screens, exposed-node74 constraint, optional helper objective, and bounded local replacement screen. All mathematics about the accepted 194-state consistency machine remains attributed to the upstream project. No accepted upstream machine table has been modified by this work.
