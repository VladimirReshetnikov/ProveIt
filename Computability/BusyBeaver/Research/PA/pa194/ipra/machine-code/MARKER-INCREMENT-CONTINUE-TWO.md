# Marker entry through increment and continue-two

`PA194MarkerIncrementContinueTwo.markerToContinueTarget` composes the genuine
non-first marker-entry execution with the concrete increment-output and
32-step continue-two controller theorems. In every candidate PRA model,
including nonstandard model values and times, it proves both the original
increment endpoint and a later dense-24 endpoint, with an existential model
clock and the exact packed tape halves stated in the theorem.

The theorem retains every premise of `markerToIncrement`: a non-first marker
index within the nine logical registers; `idx+n=7`; the stated marker-entry
file and k=1 controller shape; a positive selected value; the first physical
value `k+7`; and a blank final suffix. It adds `k=j+1`, making the returned
first physical block positive. The `k=0` branch is not covered. The theorem
exhibits the even returned-file code and preserves the exact file-layout
relations in the original marker theorem.

This is a conditional physical-machine path from the specified intermediate
marker configuration. It does not establish that the configuration is reached
from a blank tape, that `u=0` or the source-frame padding bounds hold, or that
this path simulates a source instruction. It is not an iPRA derivation or an
implication involving `Con(PA)`.

The module passed an author suffix rebuild against previously checked
prerequisite overlays. Its reported axioms were `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. The full nested checker
`check-marker-increment-continue-two.sh` is provided but has not been run.
