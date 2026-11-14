# First physical value six: all marker positions to dense 24

`PA194MarkerFirstSixPositiveTo24.markerFirstSixPositiveTo24` follows the
genuine non-first marker-entry path with first physical value six and a
positive selected value to dense 24. It uses the actual zero-length returned
first block, proves the remaining file code is even, and gives the exact
model clock and packed endpoint tape. `PA194FirstSixAllTo24.markerFirstSixAllTo24`
combines that result with the separately proved selected-zero branch. The
combined theorem covers all eight non-first positions and arbitrary selected
values, with the common controller half and an existential clock and right
half; the branch-specific theorems retain their exact equations.

The marker delimiter, nonempty following file, and k=1 controller layout are
hypotheses. Neither a blank suffix nor `idx+n=7` is required. These statements
hold in every candidate PRA model, including nonstandard model values and
clocks. They start from an intermediate marker configuration and do not prove
blank-tape reachability, a source-frame correspondence, source-instruction
simulation, or an iPRA consistency implication.

The five new modules passed an author suffix rebuild against previously
checked prerequisite overlays, with `propext`, `Classical.choice`, and
`Quot.sound` as their reported axioms and no `sorryAx`. The full nested
checker `check-first-six-all-to24.sh` is supplied but has not been run.

An independent ordered suffix replay rebuilt all five first-six modules
against separately checked selected-zero and controller objects, with retained
deeper prerequisites. It passed without `sorryAx`; this was not a full nested
replay.
