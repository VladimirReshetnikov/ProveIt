# Independent review: 21-state biased reference copier

Date: 2026-10-18. Source: `../native_copier/biased_reference_copy.py`, SHA-256
`a8a601a658215da3db6cbbfad2d02fee032ce013006d8c72befe226a99329132`.
Table SHA-256:
`cacdfb724b73262773661bdb374fead9cc92daad9aa0b5658a5cc909391b8f40`.

## Verdict

**The prepared-frame contract and nine-state component reduction are valid.**
Encoding reference r by a source field of r+3 ones lets the moving-zero loop
start directly at copied value 0, without the unbiased copier's two initial
counter increments or special cases. The exact table has 21 working states
(20 operational plus reject), 42 rows, and separate return 21. It returns a
counter of r+1 ones, restores the whole source, and preserves every other cell.
This is not yet an integrated or blank-tape proof-search machine.

## Exact theorem and universal invariant

Use the same single-one counter at c, gap of g zeros, anchor `10`, and finite
stream of earlier nonempty unary fields as in `marked_unary_copy_review.md`.
Let the selected field start at s and encode reference r>=0 by r+3 ones,
followed by a zero at s+r+3. Initially its first one s is erased. Assume
**g>=r+2**, not the stronger g>=r+4 needed to copy the full unbiased field value.
The entire exterior of [c,s+r+3] may be arbitrary.

Starting at s in `init_bias`, the machine reaches return 21 at c+r. It writes
ones at c..c+r, restores s, and leaves every other cell as initially given.
No scanned cell lies outside [c,s+r+3].

Proof. Initialization restores s, erases s+1 and s+2, and enters `next_source`
at s+3. The latter two cells are guaranteed to be one before erasure because
every encoded reference field has at least three ones, including reference 0.
For each j=0..r, the following invariant holds at `next_source`:

- head = s+j+3;
- the counter is exactly the one block c..c+j;
- the remaining counter gap has g-j>=2 zeros;
- the source has a restored one prefix s..s+j, a zero pair at s+j+1,s+j+2,
  and unprocessed ones at s+j+3..s+r+2;
- all other cells are unchanged.

Initialization establishes j=0 without a backward shuttle or counter increment.
If j<r, `next_source` reads the next source one, erases it, keeps the old right
marker zero, and restores the old left marker. It then enters `loop_ones` on
the restored source prefix, strictly left of the new marker pair. The unchanged
backward-scan lemma applies: all earlier field separators are isolated zeros,
and the gap supplies the first pair of adjacent zeros. Its continuation
`add_loop` appends one to the counter. At least g-(j+1)>=2 gap zeros remain.
The unchanged forward scan passes the anchor and all earlier nonempty fields,
then recognizes the moving zero pair and returns to `next_source`. This
establishes j+1 with all full-tape effects as stated.

If j=r, `next_source` reads the original selected-field delimiter. It restores
both marker cells, enters `done_ones` on the restored prefix, and uses the
backward scan and `return_left` to return at c+r. No exterior cell is read or
written. There are exactly r advancing iterations, and every shuttle traverses
a finite region bounded by the counter and selected field. This proves total
termination under the precondition.

References 0 and 1 are genuine instances of this induction: r=0 immediately
restores the marker pair and returns without adding a counter one; r=1 takes
exactly one advancing iteration. They require no separate states. For r=0,
minimum g=2 already supplies the two-zero gap delimiter. The capacity bound
remains substantive: the backward scans cannot generally identify a gap
reduced to a single zero.

## Accounting and integration boundary

The construction removes 12 states from the 30-state unbiased implementation
and introduces three bias-initialization states, giving 30-12+3=21. The removed
states include the old initialization, the value-1 and two-increment backward
shuttles, and their append states. The shared reject sink is counted. No
unreachable-state discount or uncharged return state explains the reduction.

Changing only reference fields to this encoding leaves them nonempty, so the
existing locator and delimiter scans remain valid. Tag fields can keep their
original encoding. The semantic arena validator, any other reader/equality
routine, and the actual source-to-numerical-node interpretation must all agree
that a reference field length r+3 means reference r. Existing raw-length
comparisons cannot be reused without checking their intended offset.

At the locator/copier interface, the enlarged gap is g+i, so the required
capacity is r+2<=g+i. Backward-reference validation may discharge this with
no extra reservation, but the precise indexing convention must be proved.
The copier still enters at the marked first cell, unlike the locator's exit at
marker+1; that adapter remains chargeable. The copier restores its marker,
and reuse still needs destination reset, marker placement and query/path
preservation. Its malformed-input sink/scans are not a fair reject-and-restart
protocol. No global state-count saving can be claimed until this encoding and
all such interfaces are integrated and charged.

## Independent executable evidence

`audit_biased_reference_copy.py` independently serializes prepared frames,
parses and simulates the exact emitted table, and compares entire tapes and
head positions. It passed 1,260 cases, including 165 each for r=0,1,2,
minimum capacity g=r+2, arbitrary earlier fields, translated origins and
arbitrary adjacent exterior bits. All 20 operational states and 30 valid
transition rows were exercised. Maximum checked length was 39,198 steps.
Results are in `biased_reference_copy_independent_audit.json` and `.log`.
These tests supplement the universal induction, and do not replace it.
The producer separately reports 1,625 tests passed.

No producer file, shared source, external repository, or user computer was
modified by this review.
