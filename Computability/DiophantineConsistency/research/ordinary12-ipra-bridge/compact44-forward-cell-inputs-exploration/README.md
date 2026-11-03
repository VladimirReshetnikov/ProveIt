# Compact44 local occupied-cell inputs

The author-side source `CompactForwardCellInputs.lean` compiles on the existing
coefficient-decoder provider. In any model of IΣ₁, each model row `a < 943` is
represented by a standard `Fin 943` index `i`. The theorem defines the
selector of `a` as a one-hot function and the 41 payload bits as the actual
model `fbit` values of `tileValue i`. It proves the selector count, selector
weighted sum and binary payload expansion required by the earlier
[conditional local aggregate](../compact44-forward-local-cell-prototype/README.md),
and concludes that the finite selector-and-copy coefficient sum equals
`1 + 2^51`. The bit-expansion proof is generic for all naturals and avoids
checking the 943 table rows individually. The table's checked payload bound is
used for the selected row.

This establishes a local fact for an arbitrary bounded model row, and so can
be applied at each bounded position of a compact word. It does **not** yet
construct a model-definable payload lookup uniformly from that word, prove
the bits correspond to the four word fields, pack those bits into the actual
compact cell, show mask/no-carry properties, construct a graph zero, bind the
retained kernel bytes, or establish an iPRA derivation. The result is a
single-side incremental proof on the existing exploratory provider, not a
fresh source-closure build or paired replay.

## Observed checks

The first two attempts exited 1: the first lacked a finite-sum conversion and
had a cast issue, and the second lacked the imported finite-sum theorem and
the base-case simplification. Both sources and logs are retained in
`observations`. The final source is exactly `/tmp/compact44-forward-cell-inputs-explore/attempt03.lean`
and was checked with Lean 4.32.0 using `-M3000 -j1 -DElab.async=false`, a
150-second timeout, and
`LEAN_PATH=/tmp/compact44-coefficient-decoder-explore/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`.
Session 2038 actually exited 0, with no warning, and the five printed axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`; none
contains `sorryAx`. The check did not request an olean output.

The source SHA-256 is
`b535716229d5754bfd0ce9e16b61996746ae60186745cb741ccab7f7ce5036d4`;
the successful log SHA-256 is
`b931ab5eb348a41b825d3e5456a192bbfceabdf628a2e895701168ec7ba9e285`.
Post-run direct provider snapshots were: `CompactCoefficientDecoder.olean`
`4e64948d97f2a22bb6fc3b45d80492b2410f6a0f8868d4b67feb020c65e39ff5`,
`Compact943Decoder.olean`
`5de069136857ac98530c177cbcba38435569202a8e8806ff9d01f5f45950e76b`,
and `ArithmeticStandardCasts.olean`
`c992bafb003c67229c756a634d31c11ecfb942839904367554488ba27ddc597a`.
The coefficient decoder hash matches the earlier occupied-cell observation;
these post-run snapshots do not authenticate complete transitive or dynamic
provider ancestry.
