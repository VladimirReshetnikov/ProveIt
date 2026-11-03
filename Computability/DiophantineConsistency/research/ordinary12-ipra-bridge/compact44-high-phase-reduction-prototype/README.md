# Finite phase reduction for the symbolic high mask

`CompactHighPhaseReduction.noCarry_of_active` proves, in every model of
IΣ₁, that a block `z < 2^(67*8807)` is binary-disjoint from the actual
symbolic finite-list `highNat` if its padding digits at phases 8792–8806
vanish and each remaining mask-supported phase has local binary no-carry.
The explicit active phases below padding are `0`, `1013–1022`, `1065–1073`,
`2195`, `3296`, `4393` and `5495`. The theorem proves the high-mask digit is
zero outside these phases and the padding interval. Its local no-carry
premises remain genuine obligations; this is not a full high-mask proof.

The proof uses the exact symbolic high-digit list, the standard-numeral
property of each model phase below 8792, and represented-block no-carry to
reassemble all 8807 digits. It does not identify the mask with retained
literal bytes or prove complete packing, graph zero, or an iPRA theorem.

Attempts 01–03 failed on list-index simplification, opacity/numeral casts or
an explicit `getD_replicate` argument; their sources and compiler logs are
retained. The corrected guarded single-author attempt 04, session `55361`,
exited 0 with no warnings or `sorryAx`; all three named axiom reports contain
only `propext`, `Classical.choice` and `Quot.sound`. Sampled direct-import
and companion hashes were unchanged. Provider source/object, package,
transitive, dynamic-loading and between-observation ancestry remains
inherited; this is not a paired replay or authenticated full closure, and
the `/tmp` paths in the runner are ephemeral.
