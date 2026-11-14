# First-three positive branch with blank tail: to dense 14

`PA194FirstThreeBlankTailTo14.markerFirstThreeBlankTailTo14` extends the
state-13 path from the genuine first non-first marker entry when the first
physical value is three, the selected value is `k+1`, and the final file tail
is zero. The actual returned file code is even, which supplies the delimiter
for the model-uniform state-13 scan through all `k` unary cells. The machine
then reaches dense 14. The theorem gives both final packed tape halves exactly,
using the input values and the existing primitive-recursive `returnCode`; the
clock is existential. No case split on the model-valued `k` is required.

The block count is a fixed Lean natural number, while block values, `k`, and
the execution clock can be nonstandard model elements. The intermediate marker
layout and blank tail remain assumptions. This is not a source-frame
correspondence, a blank-tape reachability result, or an iPRA consistency
implication.

A fresh author one-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The full nested checker
`check-first-three-blank-tail-to14.sh` is supplied but has not been run.
