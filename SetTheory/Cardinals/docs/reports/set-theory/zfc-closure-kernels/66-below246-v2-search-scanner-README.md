# The eight-zero scanner obstruction and bounded reuse searches

**Outcome.** No machine with fewer than 246 working states was obtained by
these searches. This contribution supplies an exact counterexample to a
tempting scanner simplification, a complete census of the affected instruction
paths, and reproducible bounded searches. It does not establish a state lower
bound or a new consistency-machine endpoint.

The baseline is the existing original-label context246 table, starting in
state 95 on blank tape and using separate halt label 254. Its SHA-256 is
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
The supplied baseline and instruction-site list come from the incoming
`zfc-context246` package inspected in ProveIt at commit
`8cdc55ff9281b0aaba49bf74b0b225d57f12b893`.

## A sharp obstruction within the current simulation interface

The marker-recovery routine scans left. Its state sequence for successive
zeros is

```
4, 6, 9, 13, 19, 29, 41, 58, 74
```

Every listed state restarts the count at state 4 upon reading a one. On the
ninth zero, state 74 enters state 84, which scans right to the marker and
enters dispatcher 96 on the following cell. This discussion concerns the
one-direction counting phase; it is not a minimality theorem for arbitrary
Turing-machine implementations of marker recovery.

The complete 6,460-leaf program has no zero run longer than seven. Removing
trailing zeros before measuring reduces the maximum to six. These facts alone
do **not** license an eight-zero detector. Selection changes the first phase
cell immediately after the program-counter word to zero, so a seven-zero
terminal run becomes an eight-zero run inside the finite active tape. Exactly
18 instruction leaves have such a terminal run. All are decrement instructions:
ten address logical register 1, seven address logical register 2, and one
addresses logical register 8. Their exact words and the complete histograms
are in `results/path-census.json`.

The proposed deletion is completely specified by

```
delete both rows of state 74
replace 58 0 0 L 74 with 58 0 0 L 84
```

All other rows and the old blank start 95 remain unchanged. This gives 245
working labels and 490 rows, but it fails the inherited marker invariant.
`results/rejected_scanner245.tm` is supplied as a rejected diagnostic table,
not as a candidate whose consistency calibration has been proved.

### Exact finite witness

Start a single instruction in dispatcher 96, with head coordinate 0, marker
at −1, header at 40, nine primary registers all zero, and one spare register
of value zero. The program-counter word is

```
111010010010000000
```

It is a genuine leaf of the inherited program: decrement logical register 1,
which occupies physical position 2. This is a legal input to the current
universal instruction contract. It is not asserted to occur during the
blank-tape execution.

After selection, cells 11 through 18 are zero and cell 10 is one. The reduced
detector mistakes that internal one for the marker. It reaches dispatcher 96
with head 11 after exactly **185 transitions**, while the actual marker
remains at −1. The original table reaches the correct zero-decrement successor
at head 0 after **386 transitions**, with program-counter word
`11101001001000001` and unchanged primary and spare values. The reduced table's
first, still-correct return to the root takes 102 transitions; the original
takes 104. These exact counts include every literal transition from the
stated instruction input.

`results/obstruction.json` gives the initial one-cell set, final one-cell sets,
critical state/head/read/write transitions, and dispatch visits for both
tables. The wrong recovery is a finite fact, independent of any consistency
assumption. It invalidates this reuse of the existing simulation argument.
It does not prove any statement about the modified table's halting from
blank, which could only be assessed by a different argument.

## Reproducible bounded search

The new driver first validates the baseline on all 8,391 guarded instruction
cases, with one finite register assignment per guard. It then runs three
explicit recipe families. Each candidate must pass every test in its screen;
testing stops at its first failure. The first two screens have 95 finite cases:
all 18 long-zero leaves, both decrement branches, and 45 pseudorandom leaves
using fixed seed 787. The row-freeing screen places the critical continue
site first, then tests all continue sites and the whole program if needed.
The latter order contains duplicates and totals 10,190 guarded cases.

| Family | Recipes | Surviving recipes |
|---|---:|---:|
| Delete one of 74, 58, 41, 29, 19, 13, 9, 6; replace its sole incoming action | 7,840 | 0 |
| Delete 74 with the short-scanner patch; change one additional scanner action | 19,580 | 0 |
| Try to free row 20/read-one for another purpose by redirecting its callers and repairing 141/read-one | 984 | 0 |
| **Total** | **28,404** | **0** |

An action choice includes both possible write symbols, both movement
directions, and every retained working-state target. The second family changes
one of the 20 rows of states 2, 4, 6, 9, 13, 19, 29, 41, 58, 84; it omits a
choice identical to the existing row. Its changed row can be the initially
patched 58/read-zero row, so the families overlap. Counts describe recipes,
not pairwise-distinct complete transition tables across all families.

The third family exploits the exact row equality

```
20 1 0 L 2
143 1 0 L 2
```

Eight incoming actions of state 20 encounter read-one in the inspected
instruction cases and can use state 143 for that one action. The remaining
caller 14/read-zero encounters both symbols. Its read-one cases arise through
the control shortcut at 141/read-one. The search redirects those eight callers,
replaces 20/read-one by a diagnostic halting action, and tries every action for
141/read-one. No recipe passes the screen. This is a row-reuse diagnostic on
246 labels; it does not itself delete a state. The critical continue case is
`1111100101`, a continue-level-2 leaf.

Every case has a limit of 2,400 transitions and eight intermediate dispatcher
visits. The result ledger distinguishes unexpected halts from these two
cutoffs. Most failures in the first two families are fuel cutoffs. A cutoff
does **not** prove that a candidate could never reach the target later, or
that its blank computation has different halting behavior. The recorded
negative outcome means only that no candidate passed this explicitly bounded
screen.

Each gzip ledger records every recipe and its first observed failure,
including exact program-counter word, branch, transition count, final state,
and head. The summary records SHA-256 hashes for both the uncompressed and
compressed ledgers. Gzip timestamps are fixed to zero, making release bytes
reproducible.

## What would be needed for a saving

Reducing the maximum selection-phase zero run below eight would make a shorter
detector plausible, but every recurrent phase and the new blank initializer
would still need verification. A grammar rotation might shorten the relevant
terminal paths. If it introduces one new decoder helper while deleting state
74, the count remains **246**. A genuine saving therefore requires reusing
an existing helper, making another retained decoder state unnecessary, or
obtaining more than one scanner-state reduction. Grammar reassociation also
changes program-counter updates and control exits; comparison of leaf labels
alone is insufficient to establish register-program equivalence.

More general tape encodings, simultaneous changes to arithmetic and
dispatch, and invariants that justify excluding some program sites are outside
the tested families. No global optimality claim follows from the searches.

## Replay

Requirements: Python 3.10 or later, standard library only. No network access
or proof-assistant installation is required.

```sh
python3 -B scanner_search.py
```

The default command recreates `results/`, including the three compressed
recipe ledgers. To verify only the exact counterexample and path census:

```sh
python3 -B scanner_search.py --obstruction-only --output /tmp/scanner-obstruction
```

Assertions are part of the finite checks; the driver refuses optimized Python
execution. The complete input manifest and attribution are in `NOTICE.txt`.
