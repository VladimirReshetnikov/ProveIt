# Temporal cyclic carry for the constructed compact word

`CompactWordTemporalCarry.word_temporal_carry` constructs the exact cyclic
`CarryInput` for `((K + 2^e) * C) mod (2^(67*8807*N)-1)`, where `C` is
the represented word from arbitrary Σ₁-definable row and dummy functions.
It assumes positive model length `N`; the positive modulus, size bound,
Boolean digit cap and temporal rotation bound are derived. The temporal
word is the existing rotation of `C`, not an independent input. Other-band,
bare-rotation and incoming-carry terms remain present; no conclusion about
complete product/high-mask safety, graph zero or an iPRA proof follows.

The bounded guarded single-author build exited 0 without warnings or
`sorryAx`. Its named axiom report contains only `propext`, `Classical.choice`
and `Quot.sound`, and sampled direct dependency and companion guards were
unchanged. The source, command, dependency scan, log and terminal receipt are
retained in `observations/attempt01`. Provider package, transitive, dynamic
and between-observation ancestry is inherited; `/tmp` paths may disappear.
