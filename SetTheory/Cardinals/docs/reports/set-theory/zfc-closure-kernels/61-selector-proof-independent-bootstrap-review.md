# Independent prefix247 bootstrap and logical-root audit

## Exact new machine

Take the original-label incoming prefix250 table with SHA-256
`fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43`.
Delete the six rows whose state is 0, 1, or 3. Change the single remaining
row `(60,0)` from `(0,R,0)` to `(0,R,20)`. Keep start state 97, blank tape,
and separate halt label 254.

The working set is

`({0,...,253} \ {0,1,3,5,8,43,59,85}) ∪ {255}`,

of cardinality 247. Every working state has two rows. There are 494 rows
and one halting row, inherited without altering its write or move.
All 247 working states are reachable in the unrestricted transition graph.

The new original-label table has SHA-256
`0d37614f3caf37139b0be127837630539224acd1c45d748cf5704abfc3230b42`.
The canonical table has SHA-256
`58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669`;
canonical working labels are 0 through 246, start 0, dispatcher 89,
and halt 247.

## Why the reduction can preserve the runtime

The old prefix250 zero-decrement routine already uses the new reverse carry
circuit. Consequently states 1 and 3 have no role in any of the three
new register-operation contracts. Their only outside entry is `(0,0)`.
State 0's only outside entry is `(60,0)`, at the end of a register selector.

For a well-formed selected register block `0 1^(v+1)`, state 60's zero
transition moves right onto its first one. Thus state 0 is reached reading
one whenever it is entered by a valid selector. That row is `(0,L,2)`,
identical to the read-one row of state 20. The marking contract therefore
survives replacement of state 0 by state 20. The full proof must establish
this for every physical selector and complete clean frame, and combine it
with instruction coverage. It is not justified by the observed blank run.
The runtime proof agent supplies that universal audit separately.

An exact intermediate quotient isolates the remaining finite issue. Modify
only `(0,0)` to `(1,L,2)` in prefix250 and delete states 1 and 3. The resulting
state 0 has exactly the same pair of rows as state 20. Identifying 0 with 20
is therefore an ordinary one-step bisimulation on every tape. Its quotient
is exactly the delivered 247-state table. The distinction is useful:
the first change is justified only on valid recurrent frames; the second
is an unconditional table quotient. Startup must be checked on the final
table, because the old blank bootstrap did use `(0,0)` four times.

The retimed initializer's incoming-edge proof is unaffected:
state 255 has exactly the entry `(75,0)`, and state 97 has exactly the entry
`(255,0)`. The existing two-step write-and-return argument forces every
post-initial visit to 97 to read one.

## Exact bootstrap

The final 247-state table, started at 97 with head 0 on an entirely blank
integer-indexed tape, reaches the following configuration after exactly
741,241 literal transitions, with no earlier halt:

- State 96 (canonical state 89), head -5.
- Marker -6, empty PC, header 245, head-to-header distance 250.
- Nine physical values `[0,0,0,3,0,0,3,0,0]`.
- 235 additional spare blocks, all of value one.
- 487 one-cells in total; the rightmost one is at 974.

The complete one-cell set is

`{-6,245,247,249,251,253,254,255,256,258,260,262,263,264,265,267,269}`

union

`{271+3j,272+3j : 0 <= j < 235}`.

Every other cell is zero. This is stronger than a prefix-only register
comparison: it verifies both blank exteriors and the full spare suffix.

`audit247.py` performs two independent literal runs: an original-label
sparse-set interpreter and a canonical-label dense-bytearray interpreter.
It compares their whole output tapes with the displayed set and verifies
the state bijection, totality, state count, deleted-state entry census,
exact intermediate quotient, retiming graph premises, and safe root decode.
It needs Python's standard library only and runs with assertions enabled.
These are finite computation certificates, not a proof by long simulation.

## Inherited logical calibration at the current repository pin

Current inspected revision:
`e0b512a63e2c1ca6a1698fa437b8568f1643ff6b`.
The fixed logical-to-physical map is `(6,2,0,4,3,7,8,5,1)`, so the actual root
is

`(N,T,W,A,D,H,X,Y,L) = (3,0,0,0,3,0,0,0,0)`.

The exact maintained theorem specialization is

`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0`.

It permits arbitrary numerical fields `N,A,D,X,Y,L` while fixing the top
formula, formula stack, and cached formula to the safe zero codes.
`Bisim254.prog254_halts_iff R` quantifies over every register file `R`,
so it applies to this root instead of only the public or permutation252
initial vector. Compose the two with
`WFTheory.native_refutation_iff_zf` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

`RootCalibration247.lean` records that source-level specialization. It has
not been kernel checked in this environment, which has no `lean` command.
The statement is only the logical root comparison and intentionally does
not stand in for a binary-runtime theorem.

## Proof-status boundary

The inherited permutation252 endpoint is reported and sourced as a closed
external Lean theorem. Incoming prefix250 has ordinary mathematical local
identities, a complete symbolic instruction certificate, and a set-coded
ZFC composition argument; it does not supply a new end-to-end Lean/Rocq
endpoint for its exact table. The new 247-state machine inherits those
mathematical ingredients and adds selector transport and its own exact
blank prefix. Neither construction's finite literal tests alone justify an
unbounded nonhalting equivalence.

A proof inside ZFC is a specific mathematical internalization of finite
syntax, inductive computations, completeness, and set-sized model
constructions. It is not obtained automatically from the fact that an
external Lean proof lists only `propext`, `Classical.choice`, and
`Quot.sound` as axioms. The incoming audit's set-coded construction supplies
the appropriate account of the logical bridge. The repository's stronger
PA-internal proof-code and trace comparison remains separate.

No claim of global priority, minimality, or a new kernel-checked binary
endpoint is supported by this audit.
