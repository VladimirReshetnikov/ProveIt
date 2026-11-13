# Two-row contextual folds of PA196

This extends the [one-row screen](../README.md) by allowing **both** outgoing
rows of the retained state to change. It reads the same exact PA196 table and
uses the same radius-six blank-start overapproximation, projected onto five
cells. It does not find a 195-state machine or prove a general lower bound.

Run from the repository root with Python 3.10+ and a C++17 compiler available
as `g++`:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/two-row/replay.py --output /tmp/pa196-two-rows.json
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/two-row/wide_near_misses.py --output /tmp/pa196-wide.json
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/two-row/blank_halt_control.py --output /tmp/pa196-blank-halt.json
```

The first command compiles the C++ engine in a temporary directory, pins and
validates the PA196 table, derives the 270,067-window inductive closure and its
2,774 projected five-cell contexts, and runs the complete screen. It compares
its four representative-pass rejections with an independent Python block
simulator. It also reads the pinned U209 parent from the incoming U208 archive
and verifies that the **same C++ engine recovers the known U209-to-U208
fold**. The JSON output is deterministic and matches [receipt.json](receipt.json).
The second command checks the four near misses in thirteen-cell windows and
verifies finite full-tape traces to infinite right-moving sweeps. Its output
matches [wide-receipt.json](wide-receipt.json), which records all four traces.
The third command directly replays the two `{56,96}` mutations from the blank
tape and matches [blank-halt-receipt.json](blank-halt-receipt.json).

## Search template and sound pruning

For each of the 38,220 ordered pairs of distinct working states, delete one,
retain the other, and redirect targets of the deleted state to the retained
one. Starting-state deletion is included. Replace each of the retained
state's two rows independently with any write bit, direction, and destination
among the 195 retained working states and the halt, for 784 possible rows per
read bit. There are therefore 23,492,152,320 raw row-pair choices.

At both original states, for both scanned symbols and every projected context,
the test requires a **positive block of at most 16 steps** that stays within
five tape cells and matches the parent's single-step projected state, head,
and entire tape. All rows outside the retained state are preserved except for
target redirection. Successful checks would establish blank-start halting
preservation by induction on parent steps, because the original blank run's
window belongs to the computed overapproximation. No full PA proof follows
from a table-level search.

The engine first enumerates all 29,964,480 choices for the retained read-zero
row. It executes all read-zero contexts of both merged states while treating
the read-one row as unknown. Reaching the unknown row is conservatively
accepted at this stage; a choice is discarded only if a required context
cannot match without it inside the stated window and time bound. This leaves
51,264 choices. All 784 read-one rows are then tried for each, giving
40,190,976 concrete pairs. A required representative context per source
state/read discards all but four pairs; every context is then checked for those
four. None passes. The discarded first-row choices account for the remaining
raw row pairs, so this is an exhaustive negative result **within the stated
simulation template**.

## The four near misses

The representative-pass pairs merge `{56,96}` or `{96,103}`. Both possible
orientations of each merge are tested. They agree on the first representative
contexts but leave the five-cell window on an overapproximated state-96 window
whose five-bit mask is 12 (bit `i+2` denotes offset `i`). The wider search
checks all thirteen-cell radius-six contexts of the involved states, using a
128-step limit: each pair matches either 2,080/2,176 or 416/512 contexts; the
other 96 escape the window.

For each pair, a particular thirteen-cell state-96 window (mask 203) belongs
to the computed blank-start **overapproximation**. Extend this window by
zeros outside it; its one-cells are exactly `{-6,-5,-3,0,1}`. The independent
Python checker records every step from the projected child entry. For the
`{56,96}` pairs it reaches state 35 after 36 steps; for `{96,103}` it does so
after 13. At that point every cell at or to the right of the head is zero,
state 35's zero row is `1 R 35`, and the projected parent endpoint has state
41. Thus the child moves right forever, writing ones, and never matches that
parent endpoint on this particular full tape. Neither the full tape nor this
state/window has been proved reachable in the actual blank run: membership in
an overapproximation is not reachability evidence. This is a counterexample to
the attempted local proof over all admitted window completions, not a proof
that the modified machine differs from PA196 on blank input.

Independently of that overapproximation, both `{56,96}` orientations actually
**halt from the all-zero tape after exactly 12,039 steps**. Their resulting
machines each have 195 working states and the separate halt label 196. The
blank replay verifies no earlier halt, the full final tape, and the identical
projected boundary at child step 5,624 and PA196 parent step 5,620. Thus these
two candidates do not preserve PA196's nonhalting. This finite finding gives no
halting or nonhalting conclusion for either `{96,103}` orientation.

Both `{96,103}` orientations also fail the proposed projected-step
simulation on the actual blank run. [blank_projection_96_103.py](blank_projection_96_103.py)
checks entire parent and candidate tapes at every projected boundary, arriving
at parent step 5,620 and candidate step 5,624 with parent state 96 reading 1,
head position 8, and five-cell mask 22. It then attempts 512 candidate steps
and finds no matching projected endpoint. The checked boundary tapes and trace
hashes are recorded in [blank-projection-96-103-receipt.json](blank-projection-96-103-receipt.json).
This excludes that bounded step-matching proof on blank input; the machines
could rejoin later, and no halting inequivalence follows from the witness.
Run the replay from the repository root with:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/two-row/blank_projection_96_103.py --output /tmp/pa196-96-103.json
```

The search excludes multi-parent-step blocks, different head/tape encodings,
more than one state identification, modifications outside the retained rows,
and any proof using a sharper invariant that excludes the counterexample. The
initial five-cell screen also cannot establish anything about blocks requiring
outside-window reads. The supplementary full-tape counterexamples refute the
four listed candidates for the stated overapproximation even with unbounded
block length, but do not enlarge the exhaustive search. No conclusion about
all 195-state machines follows.
