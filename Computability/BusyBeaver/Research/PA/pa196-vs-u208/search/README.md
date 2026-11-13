# Local folds of the literal PA196 table

`scan_local_folds.py` tests a restricted version of the local contextual-fold
idea used in the incoming U208 reports against jamesyc's PA196 table. The
input is the exact 392-row, two-symbol table, SHA-256
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`,
with working states `0`–`195` and separate halt `196`. The script checks the
hash, row domain, graph reachability, and exact action-preserving state
bisimulation before the contextual search.

Run from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/scan_local_folds.py --output /tmp/pa196-folds.json
```

The default table is `../../jamesyc-upstream/pa196/data/pa196.tm` relative to
this directory; use `--table` to give another copy of the *same hashed table*.
The full single-process search took roughly three minutes in the initial
experiment. The JSON includes counts, survivors, and elapsed time. Reproduction
should compare semantic fields, not elapsed time. Run `python3 -B
Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/test_controls.py`
for separate two-step-window, inductive-closure, duplicate-state, and U208
controls.

## Fold template

For each of the 38,220 ordered pairs of distinct working states, delete the
first, retain the second, and redirect every target of the deleted state to the
retained one. This includes deleting start state 0: its image is the retained
state. First test retaining both rows unchanged. Then, for each read symbol,
permit replacing the retained state's corresponding row by any legal
write/direction/target triple (two writes, two directions, and 196 destinations:
all retained states plus halt). The other retained row remains unchanged.
All ordinary rows of other states are unchanged except for the redirection.

For both source states involved, each scanned symbol, and every allowed local
tape window, the test demands a positive block of at most 16 child steps whose
endpoint matches the single parent step: projected control state, head
position, and every tape cell. During a block all reads must remain within
positions `[-2,2]` relative to its entry head. The child tape is compared on
all five cells, so no write can be hidden inside the window. By induction over
parent steps, a successful complete certificate of these properties gives a
positive-block simulation preserving the entire tape and head at boundaries,
and hence both directions of halting. The local finite checks are executable
mathematics; this script is not itself a proof-assistant kernel or an exported
PA proof.

The windows are an *overapproximation*, not sampled runs. For each target state,
the script enumerates its incoming transitions and, if necessary, those of the
predecessor state. A first incoming transition constrains the just-written
neighbor. To test a second incoming transition, it reconstructs the predecessor
tape by restoring the symbol read by the first transition, then checks the
second write. A predecessor equal to start state 0 is admitted without a second
history, and all windows at state 0 are admitted. Thus all finite runs from
state 0 on any initial tape are covered, including blank tape; many impossible
windows are deliberately retained.

The one-row search uses a conservative prefilter for the unmodified read: if
its path reaches the to-be-modified row or leaves the window, it remains
eligible. A path that neither matches nor meets either uncertainty within 16
steps cannot satisfy this window-and-step template. Remaining legal patch rows
are screened first on one representative window per source/read and then on
all windows. The direct unchanged-row search is performed independently.

## Blank-start strengthening

With `--invariant blank-window`, the script instead computes the least
abstract window reachability set from the all-zero window in state 0.
`--radius R` selects a closure radius of at least two (default 2); a wider
closure is projected back to the five cells used by the local fold test. Each
step overwrites the current bit, shifts the window with the head, and allows
both possible values for the newly exposed bit. The closure therefore contains
every actual blank-start window by induction; it need not be exactly reachable.
At radius 2 the closure contains 2,848 windows, all inside the 3,014
two-predecessor windows. At radius 6 it contains 270,067 windows, whose
five-cell projection has 2,774 windows. It includes an abstract path to halt, so it is not a nonhalting proof.
The same finite local block checks then establish a fold only from blank input.

The control reads the actual sparse-label U209 parent from
`docs/incoming/U208_ConPA_2026-10-29.zip`, member
`U208_ConPA_2026-10-29/baseline/u209.native.tm`, with SHA-256
`d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16`.
It densely relabels all 209 working states and the separate halt, constructs
the radius-2 blank-window invariant, and verifies the reported fold deleting
native 211, retaining 172, and replacing `172/0` with `0 L 217`. The local
simulation passes with block lengths 1, 3, and 7. The more general two-history
invariant includes four spurious windows that prevent this same check, which
illustrates both the value and limitations of context refinement.

## Recorded two-predecessor screen

The [receipt](two-predecessor-receipt.json) records 196 graph-reachable
working states, no nontrivial exact action-preserving bisimulation class,
3,014 allowed state/windows, no unchanged-row fold, 75,307 retained
fold/read cases after the conservative prefilter, and zero survivors among
59,040,688 explicitly tested replacement rows. The receipt was generated before
the later `--invariant` option was added, and identifies its invariant with
`predecessor_depth: 2`. The current default runs the same screen and labels it
`two-predecessor` instead.

The recorded [radius-2 blank-window screen](blank-radius2-receipt.json) has
no unchanged-row fold and no survivor among 59,054,016 explicitly tested
replacement rows, after retaining 75,324 fold/read cases in the conservative
prefilter. It was generated before the optional `--radius` and closure-size
receipt fields were added; its underlying radius-2 calculation is unchanged.

The stronger [radius-6 blank-window screen](blank-radius6-receipt.json),
produced with `--invariant blank-window --radius 6`, again finds no
unchanged-row fold and no survivor among 59,057,152 explicitly tested
replacement rows, after retaining 75,328 fold/read cases. This receipt is
produced by the current script version.

## Interpretation

This searches exact one-parent-step simulations, one control identification,
no extra helper state, at most one retained-row replacement, radius-two windows,
16-step blocks, and either stated reachability overapproximation. It may reject
a genuine fold whose correctness needs more historical information, larger
windows, longer blocks, several changed rows, nonaligned source steps, or a
more general representation. It makes no lower-bound claim for 195-state
machines, and a successful table-level fold alone would not establish the
missing arithmetic implication `Con(PA) → ¬Halt(PA196)`.
