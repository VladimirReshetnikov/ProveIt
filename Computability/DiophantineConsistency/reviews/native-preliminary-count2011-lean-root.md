# Count recovery before phase or label decoding

Date: 2026-10-25. Author and whole-source reviewer: ROOT. Independent full
source review, replay and arithmetic challenge: circuit_reduction; see
the [peer receipt](native-preliminary-count2011-lean-peer.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| NativePreliminaryCount2011.lean | ee138db4fc12507fa9dbd11c49aa6677c159bd1795588b5d0070c142e0080d2c |
| NativePreliminaryCount2011Checks.lean | 027e4d3636f4834cf8d89dbc7fe49e9b1961bb79f39ae5651926f732f9779f04 |

Both fresh root checks passed with `lake env lean -M6000 -j1` and the
independent reviewer freshly replayed both files against temporary objects.
The module emitted no diagnostics. All four axiom reports use only the
standard `propext`, `Classical.choice`, and `Quot.sound` axioms. Ancestors
and the entire umbrella were not freshly rebuilt by these checks.

The full clause mask implies the actual low-nine-bit test. Phases0..6
bound the full low part by2006 before counting; phases11 and above remove
the temporal term modulo2048 and bound the remaining part by1942. Only
phases7..10 request the483 padding-prefix masks and residue identities.
The proved staircase gives a first-prefix count at most3, total at most462,
and then low part at most2006. The clause mask forces at most one selector
in every branch, without assuming that conclusion or decoded labels.

The theorem keeps Boolean bits, carry<=57, the extra Boolean summand,
temporal scale/source and exact clause residue and mask explicit. Its
padding premises are conditional on the middle phases. The actual
physical convolution/carry and padding bindings remain required before
applying it to an arbitrary current polynomial zero.

The raw phase10 counterexample has512 selectors and clause2^45, which
passes the entire mask2^45−4. This verifies the need for the middle-phase
information in this method; it asserts no actual source solution. The
independent finite challenge covers all47 physical phases and all reduced
count/carry/unit cases, supplementing the Lean theorem.
