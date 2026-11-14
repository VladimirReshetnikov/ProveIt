# Independent proof audit: Joint U209 to U208

## Verdict and exact patch

The reduction is valid. It admits an elementary, bounded, positive block
simulation from every common initial tape in state 0, with no dependence on
the source compiler or on an experimental blank-tape invariant. The proof
uses an inductive invariant of the **old** U209 machine. The same invariant
must not be asserted for the merged U208 state 211.

The old native table is the full Joint / Compatible Folds table, SHA-256
`d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16`.
The patch is exactly:

```
delete: 172 0 0 L 67
delete: 172 1 1 R 184
change: 116 0 0 R 172  ->  116 0 0 R 211
change: 211 0 0 R 157  ->  211 0 0 L 217
```

All other retained rows are literally unchanged. The complete incoming
inventory of old state 172 contains only 116/read0, so the single displayed
redirection is exhaustive. The old and new start states are 0, and native
halt 254 is unaffected. The final table has exactly 208 working states,
416 binary transitions, and only left/right moves. Every working state and
halt are graph-reachable.

Native U208 SHA-256:
`b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135`.

Dense U208 SHA-256:
`a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1`.

The dense table sorts the surviving native working labels into 0 through
207, with separate halt 208. The independent checker validates all 416
conjugated rows and exactly matches the separately constructed candidate.

## A five-clause inductive invariant

For an old configuration with head h, write `x_i = tape(h+i)`. Associate
the following clause with the indicated state, and the true clause with
every other state:

| Old state | Clause |
|---|---|
| 116 | `x_-1 = 1` |
| 172 | `x_-2 = 1` and `x_-1 = 0` |
| 217 | `x_-1 = 1` |
| 163 | `x_-1 = 1` or `x_-2 = 1` |
| 211 | `x_0 = 1` or `x_-1 = 1` |

The initial state is 0, so the invariant initially holds on **every** tape.
Its inductive step follows solely from the complete incoming inventories:

| Destination | All incoming old rows |
|---|---|
| 116 | `215/1 = 1 R116` |
| 172 | `116/0 = 0 R172` |
| 217 | `216/1 = 1 R217` |
| 163 | `132/1 = 1 R163`; `199/1 = 1 R163`; `217/0 = 0 R163` |
| 211 | `163/0 = 0 L211`; `163/1 = 1 R211` |

For 116 and 217 the incoming right move immediately writes a left neighbor
one. For 172, the incoming right move writes its nearest left zero while
the source clause at 116 provides the second-left one. Entries to 163 from
132 and 199 write the nearest left one; the entry from 217 writes the
nearest left zero and inherits the second-left one. Finally, the right
entry to 211 writes a nearest-left one. For the left entry from 163, its
old nearest-left cell becomes the current cell, and its old second-left
cell becomes the nearest-left cell. The clause at 163 is therefore exactly
the clause required at the new 211 configuration.

This is a one-step simultaneous induction, not an assumption that enough
history has already elapsed. It handles all initial-time cases without
exceptions. In particular, it rules out a bad old 211/read-zero entry with
a zero predecessor, even though that state also has a left-moving incoming
edge.

The independent executable verification enumerates all Boolean valuations
on the window `[-3,-2,-1,0,1]`. This window contains every source clause and
every shifted target clause for moves of either sign. There are eight rows
with nontrivial target clauses and 32 valuations per row: 256 combinations,
of which 104 satisfy the source clause and read-bit premise. Every one
preserves the target clause. The other 410 old transition rows have true
target clauses and need no local restriction. Since no clause or transition
reads beyond this window, the finite truth table establishes the universal
local Boolean implication for arbitrary exterior tapes.

## Four whole-tape macro identities

Define `rho(172)=211` and `rho(q)=q` otherwise. The simulation relation at
block boundaries relates an old state q to new state rho(q), with identical
head position and entire tape. Put the old head at coordinate zero for the
following four cases.

### Old state 172, read zero

The invariant supplies cells `(-2,-1,0) = (1,0,0)`. The old transition is
`172/0 = 0 L67`. The new path, listing configurations before each step and
then the endpoint, is:

```
211@0 → 217@-1 → 163@0 → 211@-1
      → 217@-2 → 215@-1 → 157@0 → 67@-1.
```

It has seven steps. Every write preserves the bit read. Only cells -2, -1,
and 0 are read, so the entire arbitrary exterior is untouched. The final
state and head agree exactly with the old one-step endpoint.

The nested revisit to 211 at coordinate -1 is legitimate. The old-state
clause is not being asserted about this internal new configuration. Its
behavior is checked directly from the literal new rows.

### Old state 172, read one

Both old 172/read1 and new 211/read1 are `1 R184`. This is one step with
identical tape and head. The predecessor context is not needed by this
branch.

### Old state 211, read zero

The invariant supplies cells `(-1,0) = (1,0)`. The old transition is
`211/0 = 0 R157`. The new path is:

```
211@0 → 217@-1 → 215@0 → 157@1.
```

It has three steps, reads only cells -1 and 0, preserves all tape bits,
and ends at exactly the old one-step endpoint.

### Old state 211, read one

Both machines use `1 R184`, a one-step identity. No neighbor assumptions
are needed; the independent symbolic case leaves every cell except the
current one opaque.

For all 414 other old rows, the new row at rho(q) has the same write and
direction and the rho-projected target. This includes the redirected row
116/read0. The four special cases and ordinary row identities cover all
418 old state/symbol pairs.

## Halting equivalence and exact clock relation

The old invariant is preserved by every old step. Therefore every old
step at a simulation boundary can be expanded into its indicated new
block, whose length is one, three, or seven. Each block is nonempty and
has no internal halt. Induction on a finite old run gives matching entire
tapes and heads at every successive boundary.

If the old run halts, the corresponding new run halts at its final
boundary. Conversely, suppose the new machine first halts after T steps.
If the old machine had not halted in its first T steps, those steps would
produce at least T new steps, with no halt before or inside any block,
contradicting the supposed new halt. Hence the old machine halts as well.
This reverse argument is essential; forward simulation alone would not
establish the desired consistency equivalence.

For a halting old run, let `N_172,0` and `N_211,0` count its visits to the
indicated old state/read-bit pair. Then exactly

```
T_208 = T_209 + 6*N_172,0 + 2*N_211,0,
T_209 ≤ T_208 ≤ 7*T_209.
```

The counts refer to the old run, not to internal visits to merged new 211.
No new source reassociation occurs in this reduction, so this bound is
directly against the supplied Joint U209 table. The mathematical all-tape
statement uses arbitrary binary tapes; the same finite-induction proof is
formalizable in PA for the usual numerical coding of finite-support tapes
and, in particular, the blank initial configuration.

Thus the new reduction establishes a direct PA-formalizable equivalence
between blank halting of the two literal tables. The stronger endpoint
with Con(PA) inherits the old U209 numerical-calculus and Theory U/PA
calibration. This audit does not add an end-to-end proof-assistant
certificate for that separate inherited calibration.

## Independent checks and controls

`check208.py` imports no supplied proposal module and uses explicit
exceptions rather than Python assertions. Its outputs under ordinary
Python and `python3 -O` are byte-identical. It checks:

* the exact old table hash and all complete incoming inventories;
* the five-clause invariant by exhaustive local Boolean implications;
* every ordinary old row against the quotient;
* all four macros with unread exterior cells kept opaque;
* totality, state counts, native-to-dense conjugacy, and graph reachability;
* byte equality to the independently constructed native and dense table;
* twelve rejected damaged constructions or weakened-context controls.

The controls cover missing incoming redirection; wrong helper; corrupted
215/read0; restoring the old 211/read0 row; writing one instead of zero;
the wrong selector direction; the wrong shared read-one branch;
corruptions of both helper branches; the wrong final left move; dropping
the second-predecessor condition for old 172; and dropping the left-one
condition for old 211/read0.

An independent literal simulation also compared old and new configurations
after **every one of 48,140 startup transitions**. They agree exactly,
ending at native state 84, head -2, with 120 one-cells. None of the changed
or deleted rows is visited during this prefix. This extra regression is
recorded in `startup208.json`; the universal preservation theorem follows
from the invariant and macro proof, not from this prefix test.

## The alternate U208 remains distinct

The corresponding 208-state reduction of Compatibility U209 is not
isomorphic to the primary candidate. A compact rooted graph witness uses
the edge words

```
p = 00000010010000000100110111
q = 000000100100000001001101100111111110.
```

From state 0, the primary U208 transition graph sends both words to native
state 98. The Compatibility U208 graph sends p to 98 and q to 215. A rooted
read-edge-preserving isomorphism cannot send one state to both states.
These are graph paths, not asserted realizable tape executions. The
standalone `compare208.py` checks the witness and records both table
hashes in `comparison208.json`.
