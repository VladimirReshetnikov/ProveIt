# Independent finite coefficient-decomposition closure review

The source-only review passes for plan commit `28622c2888`. Independent
session 37688 exited 0; it reran the author's scan byte-for-byte and checked
the exact source against commit `d417147fec`, its three imports and three
named axiom reports, and both distinct parent audit receipts and terminal
observations. The optimized scan and optimized independent audit each exited
1 as required.

On **each corresponding side**, the decoder provider has 123 objects, the
coefficient-mass provider has 115, and all 115 shared paths have matching
hashes. The two decoder inventories also match across sides. The review
independently checked both audited seed output objects per side against their
respective audit receipts and exact source paths, their 40 source companion
slots, the 80 target/carry slots, and ten package Init slots. In particular,
Init currently has `.olean`, `.olean.private`, `.olean.server`, and `.ir`;
a future replay must guard those existing companions as well as absences.
The `CHECK.json` SHA-256 is
`72cce2c801432154f8cbac90e4ef8f238ef4e636081c5475648ce8ec0bfd43e7`.

The first draft of this independent audit exited 1 at Python parse time
because a generator expression lacked a closing parenthesis; its source is
retained under `observations/attempt01.py`. The corrected audit produced
session 37688. This review checked the two parent receipts and observations,
but did not rerun both full parent audits or launch Lean. It is an
inventory at particular times, not an atomic freeze or a paired build.

The source proves a finite model-valued weighted-sum identity for arbitrary
`f : Fin 943 → V` and `b : Fin 41 → V`; it does not assume Boolean inputs or
`NoCarry`. It does not identify the sum as a graph column, establish its
local decoder premise, bind the retained K or ports, prove machine semantics,
or produce an internal iPRA theorem. Full package/transitive/dynamic ancestry,
initial-loader and sampled-resource qualifications remain for any later
replay and artifact audit.
