# Explicit closing rows and exact helical quotient

Date: 2026-10-26. ROOT independently read the complete two main/check
packets and author receipts before fresh direct replay. All four capped
Lean commands passed, with empty main logs and31 standard-only axiom
reports. Main outputs went to separate `/tmp` objects; checks imported
frozen author objects. No complete import-closure rebuild is claimed.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942FinishConstruction.lean (164 lines) | b59a1698fdad679feb55bd6bb7a9eb440f46181204662f7245646522e403343d |
| WangTiles942FinishConstructionChecks.lean (107 lines) | 3c5a2de8e5bd3ff80c7c16e1b08728e8d94e8bb4577d9578d09244359d273c4e |
| WangTiles942HelicalQuotient.lean (147 lines) | dd7e2a20254aba54f57d03cc6690a6c18d3d45d83fe3c44383f53be4c3162481 |
| WangTiles942HelicalQuotientChecks.lean (91 lines) | 5be0501091408ae5bee59a2b863e81edc93ed3552d209d02701a2434348b8034 |

The closing-row packet constructs actual halted pass and finish rows
with north equal to the actual configuration's colors, including halted
head432/433. Pass preserves the colors; finish produces438. All horizontal
edges are zero. Actual Allowed membership requires the given halted
state; a negative check rejects passing an operating head. Arbitrary
tapes, duplicates and signed positions are retained.

The explicit initializer has Left at negative positions, Start at0,
the actual head initializer at1 and Right thereafter. It is Allowed
and horizontally matching at every integer. Its south color is exactly
the initialized actual machine encoder, including South4 at1. The
explicit reset row has edges1, north438 and south equal to the initializer
north. All finish/reset/initializer interfaces are proved, but no finite
wall or complete trace-cycle assertion is assumed or inferred.

The quotient packet starts with an actual Allowed tile plane, real
matching, Start at(0,0) and periods(w,−1),(0,H). It derives
T(x,t)=T(x+w*t,0) in both integer time directions and the row-zero period
w*H. Its signed row function agrees with canonical `ZMod` representatives.
Choosing actual table indices after fixing tile values gives the full
binding at address−x−w*t. Literal tile injectivity recovers Start index0;
the matching directions then give `MarkedWord(w*H)(w:ℤ)`.

There is no coprimality, unique-Start, run or assumed factorization
premise. Tests cover negative time, negative representatives, the
temporal sign, noncoprime dimensions and modulus1. The constant plain
examples prove quotient binding only; they are not claimed to contain
Start. Positive dimensions supply the required nonzero finite modulus.

Root commands used `lake env lean -M6000 -j1`. The twenty closing-row
and eleven quotient axiom reports contain only subsets of `propext`,
`Classical.choice`, `Quot.sound`, including some empty sets. Check logs:
`3dcd314819497808be59be4b370d99159373eef5f468202604fc6f3f6af71ce0`
and `6c8b2ce883573a06bef5ea9e047895573cad8fc637aa39c241704cacc2f86851`.
Author receipts: [closing rows](wang-tiles942-finish-construction-author.md)
and [helical quotient](wang-tiles942-helical-quotient-author.md).

These are components of the reverse construction. A complete cofinal
machine-trace plane and controller/arithmetic witnesses remain open.
The maintained decimal equation page and metrics are unchanged.
