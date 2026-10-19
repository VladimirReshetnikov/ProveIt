# Independent review: unary equality comparators and copier18

Date: 2026-10-18. Reviewed source/proofs under `../arithmetic_core`.
Exact table hashes, structural checks and independent runs are recorded in
`comparators_and_copy18_independent_audit.json`.

## Verdict

The ordinary universal proofs for comparator29, its stronger-gap comparator27
variant, and the exact copier19-to18 quotient are sound. The guard maps are
admissible under their stated entry conditions. EQ and NEQ are separate
external ports and must retain their different meanings; neither table is a
complete consistency-search machine.

- Comparator29: 28 operational states + reject; gap>=2; EQ29, NEQ30.
- Comparator27: 26 operational states + reject; **gap>=3**; EQ27, NEQ28.
- Copier18: 17 operational states + reject; separate RETURN18.

## Comparator29 universal argument

Initialization restores the selected first one and erases its following two
ones, which exist because the field has length b+3. At each normal `next_source`
entry after j successful paired consumptions, 0<=j<=min(a,b), the counter is
1^(a-j+1), its gap has grown by j zeros, and the only source changes are the
moving zeros at s+j+1,s+j+2. The head is s+j+3. All other cells are unchanged.

If j<b, the next one is erased and the old left marker restored. The backward
shuttle runs strictly left of the new marker, so its only adjacent zero pair
before the counter is the gap. It erases the rightmost counter one and tests
the preceding cell. If j<a, that cell is one; the surviving counter and the
right shuttle establish j+1. If j=a, the tested cell is precisely the required
zero at c-1, proving a<b. Restoring the counter sentinel and taking the failure
right shuttle locates and restores both moved source zeros. The failure left
shuttle reaches the single sentinel, temporarily clears it, and the clear/
restore/return sequence exits NEQ at c with that sentinel restored.

If j=b, `next_source` sees the original field delimiter. After restoring both
marker zeros, the done shuttle reaches the rightmost remaining counter one
and tests its left neighbor. A zero can occur there exactly when a=b, at c-1,
so the EQ move returns to c without altering the remaining sentinel. If a>b,
the tested neighbor is one; the counter-clear loop erases the whole remaining
finite one block, detects c-1, restores only c, and returns NEQ at c.

These cases are exhaustive, and each terminal path restores the source and
clears exactly the original counter cells c+1..c+a. Normal loops increment j
until either source completion or the single exhaustion attempt. Every shuttle
crosses finite positive one-runs with isolated separators until its specified
zero-pair delimiter. The growing gap never falls below two zeros. Thus the
argument proves termination and the exact entire-tape/head contract for all
natural a,b, not just bounded tests. Arbitrary positive-run headers, including
the seven-cell mode header, do not introduce a false double-zero delimiter.
Only c-1 is read left of c, and no cell beyond s+b+3 is read.

The two pre-fold identifications pair initialization states reading one with
`return_neq` and `restore_counter` reading zero. The four forbidden old pairs
are excluded by the field length and cleared-counter invariant. Every other
old row was checked against the projected new row, including both distinct
terminal targets. Literal-step induction transfers the exact 31-state trace
to 29 states. After folding those two states allow both read symbols; they
must not retain obsolete forced-one or forced-zero guard assignments.

The remaining seven forced-zero roles (init, back_one, restore_old_left,
restore_exhausted, failed_restore_left, restore_right, restore_left) read exactly
the designated marker or just-cleared counter cells described in the invariant.
All other states conservatively admit both symbols, including reject.

## Comparator27 extension

Only the known-a<b terminal path changes. After exhaustion, restore sentinel c
and write a dummy one at c+1. That cell is zero: it was either already consumed
from the original counter, or was initial gap when a=0. Relative to the original
loaded-counter gap g, the new two-one counter leaves g+a-1 zeros before the
header. This is at least two only under the stated g>=3 premise.

The existing failure right shuttle restores the source marker, then joins the
ordinary done left shuttle. Because the dummy counter has two ones, done_check
necessarily reads one, clears both dummy cells, restores only c and returns
NEQ. This is correct because a<b was already established. It also restores
c+1 even when that cell originally belonged to the gap. Removing three failure
left-shuttle states and adding the dummy writer saves exactly two states.
All inherited guards remain sound; the new writer reads only zero.

The gap strengthening must be checked after any prior copier loads a: allocating
an initially empty gap of a+3 suffices, while a+2 leaves only two and does not
satisfy comparator27's contract. Gap2 at a=0 is a genuine excluded case, not a
harmless off-by-one in the proof.

## Copier18 exact quotient

In the variable-anchor copier19, `after_anchor` and `find_ones` have identical
zero rows, and one rows with equal write/move and self targets modulo their
identification. All old table rows, not just reachable/guarded ones, project
to the 18-state table. Therefore the quotient commutes with each literal step
on every configuration and keeps RETURN separate. Its established prepared-
frame theorem transfers unchanged. A finite list of positive anchor/header
runs works because the shared scanner crosses their isolated separators;
this extension is already used in the reviewed encoded native edge.

## Independent executable evidence

`audit_comparators_and_copy18.py` checked all nonexcluded 31-to29 row projections,
all 19-to18 copier row projections, and exact emitted table identities. It
independently built 1,512 complete-tape cases for each comparator, with all
comparison outcomes, minimum gaps, several arbitrary positive-run headers,
preceding fields and adjacent safe exterior bits. Every saved guard was checked
throughout; the 29-state checks additionally coupled each step to its original
31-state state projection. All passed. These finite checks supplement the
universal proofs, rather than establishing their unbounded quantifiers.

Reviewed conservative guard files are
`compare_biased_counter_29_guards_reviewed.json` and
`compare_biased_counter_27_guards_reviewed.json`. No producer artifact or shared
source was modified.
