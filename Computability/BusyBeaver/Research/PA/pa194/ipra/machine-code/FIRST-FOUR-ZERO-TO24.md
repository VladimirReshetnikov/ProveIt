# First-four zero-selected marker to dense state 24

`PA194FirstFourFifteenTo24.markerFirstFourZeroTo24` proves that the genuine
first non-first marker entry with first physical value four and selected value
zero reaches dense state 24 under the stated nonempty file and header
hypotheses. Both final packed tape halves are exact. Register contents and the
existential execution time may be nonstandard in any candidate-PRA model.

The state-15 endpoint uses a different header from the first-five branch. The
proof continues through dense state 17 and recognizes a four-cell unary run,
then composes the existing marker-return and state-17 controller contracts to
reach dense 24. This establishes a conditional physical path only: blank-tape
reachability, source-frame correspondence, and both literal-machine iPRA
consistency directions remain open.

The new module passed a suffix replay against the separately checked
first-four state-15 and state-17 modules and retained deeper controller
objects. Its printed axioms contain no `sorryAx`.
`check-first-four-zero-to24.sh` specifies the full nested rebuild, which has
not been run.
