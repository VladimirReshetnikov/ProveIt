# Independent review: unary locator and oracle/locator pipeline

Date: 2026-10-18. Scope: the exact component tables in `../architectures`,
not a complete proof checker or consistency machine. Input hashes and literal
simulation results are recorded in `locator_pipeline_independent_audit.json`.

## Verdict and integration finding

The 18-working-state locator satisfies its universal valid-frame contract.
The 134-working-state selector/oracle/locator composition satisfies its stated
prepared-frame contract. Both full transition tables and their state counts
were independently checked. The 197-state blank probe also has the claimed
198-step always-halting behavior. There is no claimed sub-246 consistency machine.

**The composed interface irreversibly loses the requested path and its depth.**
For rule 3, paths `0111` and `10`, with identical index/arena, produce identical
complete exit configurations: tape, head, and state. Their emitted tag bits are
`0100` and `01`; both emit leaf code `000`, and following zero padding removes
any distinction. There are 28 same-rule collision groups, saved in
`pipeline_path_collisions.json`. Thus a later deterministic routine cannot
recover the requested path from this exit configuration alone. A retained
copy, tagged reversible output, external query state on tape, or regeneration
protocol is required, and its states/storage/entry-exit code must be charged.
This is an integration gap, not a counterexample to the currently stated
component effects.

## Locator theorem and proof

Fix i>=0, gap g>=2, and m>i records. Each record has three nonempty unary fields,
encoding values v>=0 by `1^(v+1)`, with one zero after each field. At origin h,
the counter is one on h-i through h, followed by g zeros, a one-bit anchor,
a zero separator, and the arena. The first cell of record 0 is erased to zero;
all other arena cells have their normal encoding. The cell h-i-1 is zero.
Start in state 0 with head h. Arbitrary tape outside this interval is allowed,
provided that required left boundary cell is zero.

The table returns in label 18 with head one cell to the right of the original
first cell of record i. The counter becomes exactly its original leftmost one,
all i other counter cells become zero, and the erased arena marker moves from
record 0 to record i. Every other tape cell is unchanged. For i=0 the arena is
unchanged. The execution is finite.

Proof by the following loop invariant. After k completed advances, 0<=k<=i,
the remaining counter consists of i+1-k contiguous ones with the same left end;
its k erased suffix cells enlarge the zero gap. The unique erased first-field
cell marks record k, and all earlier records are restored. State 0 scans left
through gap zeros until the rightmost remaining counter one, erases it, then
state 1 examines the cell to its left.

If another counter one remains, the advance branch scans the gap and anchor.
At each unmarked field, states `first_advance/ones_advance` pass its nonempty
ones and its single zero delimiter. The marked first field alone presents a
zero where a field's first one belongs. That zero is restored. The three skip
phases pass the remainder of the tag field and then the two following fields;
`mark_next` erases the first one of record k+1. This record exists since the
branch is taken only for k<i. The backward scan crosses only isolated zero
field separators and the isolated anchor separator until it reaches the
counter gap's pair of consecutive zeros. This pair exists because g>=2 and
the gap only grows. It then re-enters state 0 to the left of that pair. All
scanned finite regions are bounded by the named delimiter/anchor/counter cells,
so the advance terminates and establishes the invariant for k+1.

If no counter one remains, state 1 sees the required left boundary zero, and
`restore_zero_counter` restores the last erased counter one. The done branch
scans the same finite gap, anchor and earlier unmarked fields. Upon the marked
first field it leaves its zero unchanged and enters return label 18 with head
marker+1. It writes no other changes. There are exactly i advance branches and
one done branch. This proves both termination and full-tape effects. Translation
of all positions preserves the theorem.

The theorem does not require actual tag values <=3 or children to be valid DAG
indices. Those are certificate-validation obligations beyond locating a unary
record. Nor does it provide a reusable non-destructive index: the input i is
consumed and must be retained/regenerated when needed again.

## Composition theorem and exact interface

The pipeline layout, starting at coordinate 0, is:

- four preserved selector bits coding a rule from 3 through 11;
- 28 query-workspace cells starting at 4, containing a genuine root-to-leaf
  oracle path of length d<=23, then zeros;
- a counter of i+1 ones starting at 32, whose right end is 32+i;
- the locator's gap, anchor, separator, and marked arena as above.

The 12-state selector preserves its four input bits and enters exactly the
selected one of nine oracle roots with head 4. The tree-induction theorem in
`pattern_oracle_review.md` applies. The oracle writes d expected tag bits and
three leaf-code bits, then hands over at coordinate d+7<=30. The remaining
workspace through 31 is zero. The two seek states therefore reach the counter's
first one at 32, pass its nonempty one block, and step left from its right
separator to the rightmost counter one. They preserve all cells. The locator
then satisfies the theorem above with origin 32+i.

Thus at the final return, the selector remains unchanged, the first d+3 query
cells contain the oracle's output, the counter has just its leftmost one at 32,
and the arena marker has moved to record i. All exterior cells are preserved.
The final head is marker+1. This proof also shows termination on every valid
prepared frame. It does **not** traverse the actual arena path, compare a tag,
compare a repeated parameter, or establish that a proof rule was applied.

## State accounting and malformed input

The exact state partition is 91 constructor states +11 leaf emitters +17
locator operational states +1 nonhalting reject state +2 seek states +12
selector states =134. Every working state has two rows: 268 total. Label 134
is the separate return/halt; redirecting it to future code requires charging
that future code. Rules 0,1,2 (truth, MP, GEN) have no handlers yet and enter
the reject sink. Selectors 12..15 do likewise.

The locator alone has 18 working states and 36 rows, with return 18. The blank
pipeline probe adds 62 bit-writing states and one return adapter, for 197
working states and 394 rows. It halts in 198 steps with head -6. Its fixed
always-halting demonstration cannot be used as the consistency search startup.
The nominal 111 states remaining below 246 for the 134-state prepared component
must still cover all omitted runtime, search, startup and protocol machinery.
No free root selector, loop, return adapter, marker repair, or input validation
may be assumed.

These tables have **no total reject-and-restart contract** on malformed input:

- All-zero input to the locator follows its state-0/zero left-moving transition
  forever, without even reaching the explicit reject state.
- A well-shaped one-record arena with requested index 1 enters locator reject
  state 17 after 16 steps and then scans right forever.
- Rule 0 on all-zero input enters pipeline reject state 119 after four steps.
- A missing anchor can make the gap scan go right forever.

A fair global enumerator must never lose all later candidates to such an input.
It must either validate/generate only valid frames before invoking the component,
or provide a fully terminating bounded/restarting failure protocol covering
all malformed cases, including out-of-range references. Replacing the explicit
reject sink alone would not cure the other unbounded scans. Finite fuel in a
Python harness is not a binary-machine reject/restart mechanism.

## Independent executable evidence

`audit_locator_pipeline.py` independently parses the emitted tables, independently
serializes the unary frames, and checks sparse full tapes including nonblank
exterior context at translated origins. It also independently enumerates the
syntax trees' leaves and expected tag bits, rather than trusting producer DFS.
Results: 6,735 locator contexts and 2,280 pipeline contexts passed. The 197-state
blank table was independently simulated and checked against its full translated
prepared-run result. The path collision was checked on complete literal-run
exit configurations. Malformed sink examples were reproduced separately.
These tests support the universal proofs above; they are not their substitute.

The earlier `pattern_oracle.py` harness issue has been fixed: it now explicitly
rejects `python -O`. The new locator and integration harnesses do likewise.
No producer files, shared source, external repository, or user computer were
modified during this review.
