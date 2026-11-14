# First-three positive branch: exact dense-7 left tape

`PA194CarryThreeExactFile.carried` explicitly folds the fixed finite list of
remaining block values into the left tape. `carryThreeAcrossExact` proves that
this fold gives the exact left half after the dense-3 carry traversal, under
the even-tail hypothesis. The recursion is on the external Lean natural
number `n` of encoded blocks; each block value and the execution clock may be
nonstandard elements of the candidate PRA model.

`PA194FirstThreeBlankTailExactTo7.markerFirstThreeBlankTailExactTo7` composes
that result with the genuine first non-first marker path when the first
physical value is three, the selected value is positive, and the final file
tail is zero. It reaches dense 7 with right half 13 and the exact folded left
half stated in Lean. The clock remains existential. This refines the earlier
existential-left theorem and covers all `n` remaining encoded blocks in the
stated layout.

The assumed intermediate layout and blank tail have not been established for
a reachable source run; this result does not identify a source frame or
operation, or prove an iPRA consistency direction. The existing `sevenTo24`
contract expects an even right half and therefore does not directly apply to
this endpoint.

A fresh author two-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The full nested checker
`check-first-three-blank-tail-exact-to7.sh` is supplied but has not been run.
An independent ordered suffix replay rebuilt these two modules and the three
blank-tail prerequisites against separately checked positive-path and
marker/controller objects and retained deeper overlays. It passed without
`sorryAx`; this was not a full nested replay.
