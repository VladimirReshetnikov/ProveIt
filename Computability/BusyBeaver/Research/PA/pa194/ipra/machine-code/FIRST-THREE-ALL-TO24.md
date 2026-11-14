# First-three marker, all selected values: to dense 24

`PA194FirstThreeAllTo24.markerFirstThreeAllTo24` combines the selected-zero
and selected-positive branches of the first non-first marker when the first
physical value is three. Under the stated genuine intermediate marker and
nonempty-file layout and a zero final file tail, it reaches dense 24 for any
selected value. The final left half is exactly
`2*zeros(2, zeros(6, u))+1`; the clock and right half are existential. The
separate positive theorem gives an exact right half. The separate zero theorem
has weaker hypotheses and does not require a blank final tail.

The fixed finite block count is a Lean natural number; file values, selected
value, and clock can be nonstandard in a candidate PRA model. This conditional
physical execution does not cover the other non-first marker positions for
first value three and does not establish source-frame correspondence,
blank-tape reachability, or an iPRA consistency implication.

A fresh author one-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The full nested checker
`check-first-three-all-to24.sh` is supplied but has not been run.
