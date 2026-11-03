# Compact44 sparse target block and symbolic high-mask no-carry

On the author-side provider of the compiled word-cell client,
`CompactWordTargetNoCarry.lean` proves a concrete part of the converse
packing argument in each model of IΣ₁. Define a block of 8,807 radix-`2^67`
digits that is zero except for `1 + 2^51` at positions 4393 and 5495. The
source proves:

* the two nonzero digits equal the selector-and-copy aggregate associated
  with any bounded cell of a `CompactWord`;
* this sparse block has no binary carry against the actual symbolic compact44
  high mask `highNat`; and
* repeating the sparse block and high mask with block width `67*8807` preserves
  no-carry for every model length, including zero and nonstandard lengths.

The proof uses the actual symbolic high-mask digits at the two positions,
the finite standard bit-disjointness certificate, internal digit concatenation
and the all-model represented block sum. The no-carry claim is for this
**sparse target block**: it does not assert that the full packed kernel
product, its incoming carries or any other target columns equal this block.
It gives no full normalized cell, graph zero, retained-byte binding or iPRA
proof.

## Observations and limits

The first bounded attempt, session `67098`, exited 1 with missing explicit
packing import/namespace and definability errors; it produced no accepted
theorems. The second, session `61345`, exited 1 with numeral-cast and
definability-instance errors and a linter warning. Their exact source and
logs are retained under `observations/`. The final source is byte-identical to
attempt 03; session `34857` actually exited 0, with no warnings or `sorryAx`.
Its five printed axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound`. Lean was run with `-M3000 -j1 -DElab.async=false`, a
120-second timeout and
`LEAN_PATH=/tmp/ipra-compact-word-cell-author-01/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`;
this check did not request an output object.

Final source SHA-256:
`a37226b689090e7f8d901501902a3073aac22b357208d5a4d74c5107baa8b8d5`.
Final log SHA-256:
`bc59f4faac2e4f32afd34fdb20c32db83cce66ab3b6b132033c842a507949713`.
Post-run direct object snapshots were `CompactWordCellClient.olean`
`56ced49c140437f4080d25499828285386e881389e6ea6a418e18dab3d46bed8`,
`HighMaskLocal.olean`
`f6af3071f7e839768584ca83d0088024625d2fe4b7366651fee95dfc38f11b95`, and
`ArithmeticPackingBlocks.olean`
`467c4fc922b28cb71ac3e9b31e78e0748b3ad362d828a266dd5181684e3f3004`.
These are post-run observations, not a recorded dependency-resolution guard.
The successful check is a single-author incremental run; no paired replay,
independent Lean reconstruction, complete transitive or dynamic ancestry
audit is asserted.
