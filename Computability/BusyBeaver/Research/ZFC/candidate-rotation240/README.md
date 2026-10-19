# Source-rotation 240-state candidate

This binary, single-tape machine has **240 working states**, including
initialization, plus a separate halt state. It starts in state 0 at head 0
on an all-zero two-way infinite tape. Every transition moves left or right.
The complete 480-row table is [zfc_rotation240.tm](zfc_rotation240.tm).

The construction from commit `e5c2b3337e` combines a source-program rotation
with a further state fold on the [241-state candidate](../candidate-fold241/README.md).
Independent ordinary mathematical review and fresh executable checks support
its inherited equivalence between nonhalting and Con(ZFC).
**A complete Lean theorem for this exact 240-state machine and the equivalence
inside PA remain open.** The [compensated244 theorem](../compensated244_binary.md)
is the closed external Lean baseline. No absolute consistency, unconditional
nonhalting, minimality or two-sided independence from bare consistency is claimed.

## How the state is saved

First, rotate a transfer-plus-one loop at four occurrences in the register
program. Both forms send `(R5,R6)=(a,b)` to `(a+b+1,0)` and leave every
other register unchanged. The corresponding binary table changes only
`142/0: 0R37 → 0R72` and `142/1: 1R72 → 1R17`, keeping 241 states.
The expanded source shrinks from 6,459 to 6,455 leaves.

The rotation changes how state 72 is entered. On the rotated machine,
states 55, 142 and 90 imply a 1 immediately left of the head; state 72
implies left bit 0 and two-left bit 1. This invariant permits state 90
to share state 72. Delete 90, redirect `79/1` to 72, and change the two
rows of 72 to `0L144` and `1L36`.

| Old rotated control | Read | New path | Steps |
| --- | --- | --- | ---: |
| 72 | 0 | 72 → 144 → 47 → 15 → 32 → 46 → 17 → 106 → 93 → 57 | 9 |
| 72 | 1 | 72 → 36 → 53 → 64 | 3 |
| 90 | 0 | 72 → 144 → 82 → 93 | 3 |
| 90 | 1 | 72 → 36 → 54 → 71 | 3 |

Each path reproduces the old transition's complete tape and head position.
All other steps agree through the map `90 → 72`. The invariant holds
at inherited start 95 for arbitrary tapes, so positive block simulation
proves halting equivalence between the rotated241 and final240 machines.
The change from the original241 machine to rotated241 additionally uses
source equivalence, runtime correctness and blank initialization.

This keeps the earlier 27/15 and 39/17 savings. The source rotation alone
already appeared in source74 of the preceding intake; the new result is
its concrete combination with the 72/90 fold. The 6,455-leaf source list
is byte-identical to source74's `rotate_h` list.

## Verification

Root freshly ran ten substantive jobs, including two complete unbounded
register/list runtime checks. The final machine passes **8,386 guarded
cases and 2,322,575 symbolic rules**, exercises all 480 transition rows,
and has minimum certified instruction duration 13. Its entire generated
case array matches the delivery. Independent local checkers verify
7,640 invariant/block cases and all four exceptional paths.

Sparse and dense startup checks agree on the complete tape after
**409,691 steps**: head −5, marker −6, header 176, 351 one-cells,
logical registers `(3,0,0,0,3,0,0,0,0)` and 167 spare blocks of value 1.
The rotated241 startup takes 408,941 steps. The 750-step difference equals
`8·74 + 2·(37+18+24)`, from the four exceptional visit counts.

See the [actual replay](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake170-fresh-replay.json),
[mathematical reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-170.md)
and [reproduction instructions](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-170-reproduction.md).
These checks support ordinary proofs; they do not supply a Lean or PA endpoint.
The [source-rotation Lean proof](../source_rotation240.md) now establishes
halting equivalence for every initial register file, using the generic loop
and context theorems and changing one shared program node. Its 10 theorem
probes and 13 typed callers pass with zero warnings. Binary runtime coverage,
initialization and consistency composition still need proofs for the changed
table and source.

## Exact files and attribution

| File | Meaning |
| --- | --- |
| [zfc_rotation240.tm](zfc_rotation240.tm) | Canonical table: states 0–239, start 0, dispatcher 84, halt 240. |
| [zfc_rotation240_old.tm](zfc_rotation240_old.tm) | Inherited labels: start 95, dispatcher 96, halt 254. |
| [rotated241_old.tm](rotated241_old.tm) | Intermediate table after the source rotation, before deleting 90. |
| [sites_logical.json](sites_logical.json) | Exact 6,455-leaf source. |
| [renumbering.json](renumbering.json) | Canonical state bijection. |
| [construction.json](construction.json) | Fresh reconstruction of all five edits, one deletion and source changes. |
| [provenance.json](provenance.json) | Exact inputs, placement and fresh review evidence. |

Canonical SHA256:
`508b55a6dfdf96a42f09c49e410e078ae7478a1d0257d78d25503b4da24541cd`.
Inherited SHA256:
`547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f`.
Each noncomment row is `state read write direction next_state`.

The original calculus, program and 254-state construction are credited
to Mira-Cult, upstream verification to Jeff Ketchersid, and the compiler
framework to Andrew James Wade. ProveIt and earlier incoming reports retain
credit for the preceding reductions. The new composition and rational-cut
model study belong to the incoming240 report; no personal author is inferred.
See its unchanged [attribution](ATTRIBUTION.md). Original licenses and notices
are retained under `licenses/` without relicensing inherited material.
