# Constructing the compact44 exact-product carry input

The author-side `CompactConstructedCarryInput.lean` checks two steps toward
discharging the hypotheses of the
[word/product-column client](../compact44-word-product-column-prototype/README.md)
in every model of IΣ₁:

* If a Σ₁-definable cell function `X` has `X(j) < 2^(67*8807)` for `j<N`,
  then its represented block sum `C = bsum (67*8807) X N` has, at
  `8807*j+p`, exactly the `p`th radix-`2^67` digit of `X(j)` for `j<N` and
  `p<8807`. A cell-wise bound of three on all those digits transfers to the
  whole packed word. In particular, the earlier packed selector and copy-bit
  hypotheses follow from the corresponding **local cell** digit identities.
* For `n>0`, positive cyclic modulus `M=2^(67*n)-1`, `C<2^(67*n)` with all
  radix digits at most three, and `T<2^(67*n)`, the source constructs the
  existing heterogeneous `CarryInput` with bound `1` for the **exact**
  output `((paramKernel rho)*C+T) mod M`. It derives the band congruence from
  the existing symbolic-kernel decomposition and the cyclic rotation
  identities; the temporal digit cap follows from the digit bound. No graph
  zero or zero incoming carry is assumed.

These are conditional model statements. The source does not construct `X`,
prove the local selector/copy identities or cell-wise digit bounds, identify
the arbitrary bounded `T` with the required temporal multiplication, or
prove the remaining mask and packing conditions. Other reflected bands,
bare rotations, temporal digits and incoming carries remain present in the
product-column formulas. No graph zero, retained-byte identification or
internal iPRA derivation follows yet.

## Observed checks

Session `8935` exited 0 and printed five axiom reports, but also emitted an
informational `ring` diagnostic; its exact source and log are retained as
attempt 01. Replacing that tactic by `ring_nf` produced the final source,
byte-identical to attempt 02. Session `23008` actually exited 0 with only the
five expected axiom reports, no warnings and no `sorryAx`; the reports list
`propext`, `Classical.choice` and `Quot.sound`. Lean used
`-M3000 -j1 -DElab.async=false`, a 120-second timeout and
`LEAN_PATH=/tmp/ipra-compact-word-cell-author-01/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`.
This source check did not request an output object.

Final source SHA-256:
`b7960215516fe894e783a94994c803597cca79586f21ba6f842c4583cfa3eff2`.
Final log SHA-256:
`f8f901e2c0ae477d7f193c7b9c5492fed6059236c33211a712b0ac80516ded8c`.
Post-run direct object snapshots were `CompactWordCellClient.olean`
`56ced49c140437f4080d25499828285386e881389e6ea6a418e18dab3d46bed8`,
`CompactTwoBandCarry.olean`
`1ca025d6d666d41cdba49dd7d3b8fa3304f634591e8a0ee128fbf941f333a9d3`,
`SymbolicKBandDraft.olean`
`90516e7b8ec94eb0f4b917979e0c2800c4e8b2c1c3362ea5131baa631415402f`, and
`ArithmeticPackingBlocks.olean`
`467c4fc922b28cb71ac3e9b31e78e0748b3ad362d828a266dd5181684e3f3004`.
These hashes are post-run snapshots, not an authenticated dependency-resolution
guard. This is a single-author incremental check, with no paired replay or
complete project/package/dynamic ancestry audit.
