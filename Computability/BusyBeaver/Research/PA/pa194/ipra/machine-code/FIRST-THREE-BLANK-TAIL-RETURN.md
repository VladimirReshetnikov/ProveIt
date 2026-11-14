# First-three positive branch: return across the file

`PA194CarryThreeLeftCode.carried_eq_leftCode` proves that the earlier explicit
finite-file carry fold, when begun with an odd left half, is the existing
primitive-recursive `leftCode` applied to the original block values. This
matches the input of the previously checked `modelReturnFile` theorem.

`PA194FirstThreeBlankTailReturn.markerFirstThreeBlankTailReturn` composes that
normalization with the genuine first non-first marker path when the first
physical value is three, the selected value is `k+1`, and the final file tail
is zero. It crosses the fixed finite file and returns across every encoded
block to dense 7. The theorem gives the exact resulting left half and the
right half in terms of the existing primitive-recursive `returnCode`; only
the overall clock is existential. The physical block count is the fixed
external Lean natural number `n+1`, while block values and clocks may be
nonstandard elements of a candidate PRA model.

`markerFirstThreeBlankTailHeader` continues across the remaining selected
unary run, reaching dense 7 with left half `a2+a2` and right half
`(w+w)+(w+w)`, where the complete definitions of `a2`, `w`, and the input
layout are in Lean. This even/even boundary admits further existing controller
lemmas. Neither result establishes a reachable source frame or a source
instruction transition, nor either iPRA consistency implication.

A fresh author two-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The full nested checker
`check-first-three-blank-tail-return.sh` is supplied but has not been run.
An independent ordered suffix replay rebuilt both modules against separately
checked blank-tail, carry, and earlier marker/controller objects and retained
deeper overlays. It passed without `sorryAx`; this was not a full nested replay.
