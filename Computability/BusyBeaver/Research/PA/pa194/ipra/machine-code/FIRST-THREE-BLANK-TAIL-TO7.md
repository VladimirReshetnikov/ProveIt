# First-three positive branch with blank tail: to dense 7

`PA194CarryThreeOddFile.carryThreeAcrossOdd` strengthens the finite-file carry
invariant: after crossing the initial unary block and every one of the `n`
following encoded blocks, it returns to dense 3 with an odd left half and
right half equal to half the final tail. The external block count `n` is a
fixed Lean natural number. All block values and the execution clock may be
nonstandard model elements. The separate five-step theorem
`PA194ThreeBlankTail.modelThreeBlankTail` follows an odd-left, zero-right
dense-3 configuration to dense 7 with right half 13.

`PA194FirstThreeBlankTailTo7.markerFirstThreeBlankTailTo7` composes these
results with the genuine first non-first marker path, with first physical
value three and positive selected value. When the final file tail is zero,
the machine reaches dense 7 with right half 13; the left half and clock are
existential. The full initial tape and marker assumptions are stated in Lean.
The proof covers all `n` remaining encoded blocks in that layout.

This is a conditional physical execution in each candidate PRA model, not a
proof that the marker configuration or blank tail is reachable, a source-frame
correspondence, or an iPRA consistency implication. Its existential left half
also leaves the next controller and source-frame correspondence open.

A fresh author three-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The full nested checker
`check-first-three-blank-tail-to7.sh` is supplied but has not been run.
