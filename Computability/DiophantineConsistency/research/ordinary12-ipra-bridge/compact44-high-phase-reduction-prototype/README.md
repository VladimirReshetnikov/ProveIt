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

`CompactMarkedHighReduction.marked_high_of_active` applies the general
result simultaneously to the actual marked base and Boolean-pulsed words.
It derives both the block-size bound and the zero-padding facts from the
checked marked-word size clients. The two remaining hypotheses explicitly
require local no-carry at the listed active phases for the respective words;
neither full high-mask disjointness nor those local checks is assumed proved.

Attempts 01–03 failed on list-index simplification, opacity/numeral casts or
an explicit `getD_replicate` argument; their sources and compiler logs are
retained. The corrected guarded single-author attempt 04, session `55361`,
exited 0 with no warnings or `sorryAx`; all three named axiom reports contain
only `propext`, `Classical.choice` and `Quot.sound`. Sampled direct-import
and companion hashes were unchanged. Provider source/object, package,
transitive, dynamic-loading and between-observation ancestry remains
inherited; this is not a paired replay or authenticated full closure, and
the `/tmp` paths in the runner are ephemeral.

The first marked specialization failed only on the unnormalized model
numerals `67*8807` and `590069`. Its corrected guarded attempt 02, session
`38791`, exited 0 without warnings or `sorryAx`, and its named axiom report
contains only the same three Lean metatheoretic axioms. The checked
three-provider overlay had 524 distinct names, 339 overlaps and 338 names in
all three providers; the corresponding provider hashes and sampled direct
guards were unchanged. This incremental join has the same ancestry and
independence limitations as above.
