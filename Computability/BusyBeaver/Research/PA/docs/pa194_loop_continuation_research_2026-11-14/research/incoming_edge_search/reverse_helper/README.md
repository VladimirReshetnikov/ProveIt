# Targeted reverse-reader and shorter-scanner exploration

**Status: interrupted exploratory search; no accepted machine.**

The optimizer was requested to run for 480 seconds. Its execution/session
handle was subsequently lost. The last completed log checkpoint records
2,260,000 proposals at 209.415 seconds; there is no `DONE` record. The best
reported penalized score was 65, from an effective reader contribution of
61 and a constraint penalty of 4. The target effective contribution for
193 total states was 59, with zero penalty. No candidate hit was retained.
The recorded best grammar is an inadmissible search object, not a proposed
consistency machine. No completed 480-second negative result is claimed.

## Why this instance differs from the earlier scanner searches

The loop-continuation reassociation of LC lowers the maximal trailing-zero
count of increment paths inside `node65` and `node75` from three to two.
We combined that change with the previously recorded root and MP source
rotations and deleted native return-scanner control 34.

The root rotation reverses the history bit with which `node20` enters the
shared reader 69. The seed uses a new direct reader 334 with successors
`(90,92)` and changes the zero row of 69 to `0 L 334`. To make that sharing
correct, the AX occurrence of `node72` must now be a right child. This is
enforced separately in the grammar fitness.

The AX macro word originally contains adjacent `node65,node75`, where
`node75=(node74,node65)`. Replacing that pair by `rev75,node65`, with
`rev75=(node65,node74)`, preserves the expanded primitive instruction
sequence. Reader 334 is also the literal decoder for `rev75`, so its state
cost is explicitly included. The fixed part has 134 controls after the
scanner deletion and helper addition.

## Seed and acceptance constraints

The seed's complete 3,673 resolved primitive instructions agree exactly
with the primary source. Its 195-state folded table passes the local fold
identities but fails 76 of the 4,780 symbolic source outcomes. Every failure
is in the AX region; the changed fixed region's contracts pass. The seed is
rejected and has no claimed blank-start calibration.

The search uses exact macro attributes derived from the new loop's expanded
source. Its constraints require maximum address zero run five, maximum
trailing-zero run four for an increment address, and AX-tree height at most
38. The full AX prefix is `101101001`: its final one separates its zero
runs from those of the AX tree, and its length nine gives total path length
at most 47. `node72` and `node142` must both have history bit one.

The six macro-parameter orders are held fixed. The former free increment
reader aliases `(61,99)->330` and `(99,99)->190` are disabled, because
native 330 now implements a different loop fragment and 190 is absent.
The valid free pair `(61,61)->99` remains available. A wider pool of nearby
scores is retained during the search. The logged cycle label remains zero
because its increment was inside the disabled permutation branch; the
proposal and elapsed-time fields are the actual progress indicators.

Fitness does not prove a transition table correct. Any hit would still
require complete source-graph identity, simultaneous-fold validation, all
4,780 physical source contracts, and an exact valid blank initialization.
None was accepted here.

## Reproduce an independent bounded run

The search itself is self-contained and needs a C++17 compiler:

```sh
g++ -O3 -std=c++17 search.cpp -o search
./search seed/template.txt seed/leaf_attrs.txt fresh_run 60 261114193
```

The last two arguments are the requested time in seconds and random seed.
Timing and proposal counts depend on the computer. This command starts a
new run; it does not turn the interrupted log into a completed experiment.

`seed/` includes the exact numeric template, macro attributes, source
grammar and DAG, primitive instructions, raw and folded tables, fold list,
and failed-outcome receipt. `search_receipt.json` records the observed
checkpoint. `run480.best.grammar.json` is the last saved fitness improvement.

The optimizer is adapted from the supplied
`pa1944l_research/search/search_triple.cpp` and `screen_triple.cpp`, with the
constraint, cost-model, and pool changes described above. The encompassing
package preserves the inherited source attributions and licenses.
