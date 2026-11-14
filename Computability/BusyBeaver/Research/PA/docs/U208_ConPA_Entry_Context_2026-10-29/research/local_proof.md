# A two-cell-context reduction from U209 to U208

## Exact machines

Baseline: the Joint U209 native-label machine at
`sources/U209_ConPA_Joint_2026-10-29/U209_ConPA_Joint_2026-10-29/machine/u209.native.tm`,
SHA-256 `d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16`.

Candidate native SHA-256:
`b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135`.
Dense SHA-256:
`a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1`.

The candidate has 208 working states, 416 transitions, initial state 0,
blank symbol 0, and a separate halt label. In native labels halt is 254;
in dense labels it is 208. Native labels are names, not a census.

Write A for the old U209 machine and B for the candidate. Define
rho(172)=211 and rho(q)=q for every other state, including halt.
For every old row except those at 172 and 211, retain the row with its target
projected by rho. Delete both rows of 172 and set

```
B(211,0) = (0,L,217)
B(211,1) = (1,R,184).
```

Equivalently, besides deleting 172, only two retained rows change literally:
`116/0: 0 R172 -> 0 R211`, and `211/0: 0 R157 -> 0 L217`.
No source program or source address changes.

## Reachability invariants in A

These invariants hold for every visit during a run started in state 0, on
any initial tape. They are not inferred from a finite blank simulation.
Write h for the current head and t(i) for the tape symbol at i.

(I) If A is at 172, then t(h-2)=1 and t(h-1)=0.

(II) If A is at 211 and t(h)=0, then t(h-1)=1.

The following lists are the COMPLETE incoming inventories, checked against
all 418 old rows:

```
In(172) = {116/0: 0 R172}
In(116) = {215/1: 1 R116}
In(211) = {163/0: 0 L211, 163/1: 1 R211}
In(163) = {132/1: 1 R163, 199/1: 1 R163, 217/0: 0 R163}
In(217) = {216/1: 1 R217}.
```

For (I), the last two transitions wrote the asserted bits and then moved
right twice. Neither 172 nor 116 is initial, so these predecessors exist.

For (II), a last transition 163/1 writes the asserted predecessor one
immediately. Otherwise the last transition is 163/0 from head h+1. It writes
zero at h+1 and leaves t(h)=0 unchanged. Thus the incoming transition that
entered 163 wrote zero at h. Of its three incoming transitions only 217/0
writes zero. That visit to 217 in turn came from 216/1, which wrote one at
h-1. The last two transitions do not touch h-1. None of 211,163,217 is
initial, so all three predecessors exist.

This is why the earlier one-incoming-edge tag search missed the reduction:
211 has both left and right entries. Its useful invariant is conditional on
the current read bit and follows from three transitions of history.

## Complete local simulation

Translate an old configuration by applying rho to its control state while
leaving the head and entire tape unchanged. For an ordinary old row
(q not in {172,211}), one candidate transition produces exactly the
translated old successor. There are 414 such rows.

The four exceptional cases are as follows. All coordinates are relative to
the old head h=0. All displayed transitions preserve the scanned bit.

### Old 172, read zero

Use t(-2)=1, t(-1)=0, t(0)=0. The one old step ends at 67@-1.
The candidate follows:

```
211@0 --0 L--> 217@-1
217@-1 --0 R--> 163@0
163@0 --0 L--> 211@-1
211@-1 --0 L--> 217@-2
217@-2 --1 R--> 215@-1
215@-1 --0 R--> 157@0
157@0 --0 L--> 67@-1.
```

This is seven candidate steps. It reads exactly positions -2,-1,0, preserves
all three, and neither reads nor changes the exterior. Its internal return
to 211 is executed using the new literal row. No proof assumes the old 211
row is still available, and there is no circular macro expansion.

### Old 211, read zero

Use t(-1)=1,t(0)=0. The one old step ends at 157@1. The candidate follows:

```
211@0 --0 L--> 217@-1
217@-1 --1 R--> 215@0
215@0 --0 R--> 157@1.
```

This is three candidate steps, preserves the entire tape, and reads no
unspecified cell.

### Either old 172 or old 211, read one

The old and new rows are both `1 R184`; one candidate step suffices.

Each block is positive, has at most seven steps, has no internal halt,
and ends in the exact translated old successor. The local checker records
every literal transition and verifies whole-tape equality with arbitrary
untouched exterior. Its hypotheses are derived from the old transition
graph above; they are not accepted as unproved runtime assumptions.

## Halting equivalence and exact clocks

Induct on old steps. Invariants (I) and (II) justify the applicable local
block at every old synchronization point. Concatenating these blocks gives
the unique candidate run, with identical tapes and head positions at every
synchronization point. Determinism matters here: there is not an additional
candidate behavior beyond the concatenated blocks.

If A halts, its projected run in B halts. Conversely, suppose B halts after
T transitions. If A had no halt within its first T transitions, their
positive simulations would cover at least T candidate transitions and
contain no halt, contradicting B's halting at T. Hence A halts as well.

Thus, for every common initial tape in state 0,

`Halt(B) iff Halt(A)`.

On any halting old run, let n172 be the number of old 172/read-zero
transitions and n211 the number of old 211/read-zero transitions. Then

`T_B = T_A + 6 n172 + 2 n211`, and `T_A <= T_B <= 7 T_A`.

All invariants and simulations use only fixed finite tables and finite
induction. With an arithmetical coding of finite-support tapes and finite
run histories, the blank-tape halting equivalence has a direct PA proof.
This packet supplies the mathematical proof and executable finite local
certificate, not a kernel-checked exported PA derivation. It inherits any
separate U209-to-Con(PA) calibration obligation unchanged.

## Verification and search scope

`build_u208.py` binds the parent by its SHA-256, checks the complete incoming
inventories, constructs the exact quotient, checks all 414 commuting rows,
executes all four exceptional blocks on their fully specified read windows,
checks census/targets, and emits both transition tables and the certificate.

Discovery used finite predecessor-cylinder overapproximations of reachable
local tapes and a bounded helper search. Accepted folds then undergo exact
symbolic local checks; random screens never establish acceptance. The final
proof uses only the two elementary invariants above, so the final result
does not depend on the discovery program or random seed.
