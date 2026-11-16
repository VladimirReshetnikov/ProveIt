# First physical value five: all marker positions to dense 24

`PA194FirstFiveFifteenTo24.scanExitTo24` gives an exact all-model continuation
from the dense-15 output of a positive-length dense-84 scan to dense 24. Its
model-valued scan parameter, clock, and tape halves are stated in Lean.
`PA194FirstFiveAllTo24.markerFirstFiveAllTo24` composes that continuation with
the actual first-value-five marker paths for all eight non-first positions
and arbitrary selected values. The combined result gives the common controller
half and existentially quantifies the clock and right tape half; the separate
scanner and return lemmas retain their exact equations.

The marker delimiter, nonempty following file, and k=1 controller layout are
hypotheses. The result holds in every candidate PRA model, including for
nonstandard model values and clocks. It starts from the stated intermediate
marker configuration and does not prove blank-tape reachability, a source
frame correspondence, source-instruction simulation, or an iPRA consistency
implication. First physical values below five and the separate first-value-six
positive-selected branch are not covered by this theorem.

The two new modules passed an author suffix rebuild against previously
checked prerequisite overlays, with `propext`, `Classical.choice`, and
`Quot.sound` as their reported axioms and no `sorryAx`. The full nested
checker `check-first-five-all-to24.sh` is supplied but has not been run.
