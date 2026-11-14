# First physical value three: first non-first marker split

`PA194FirstThreeFirstSplit.markerFirstThreeSplit` follows the genuine first
non-first marker entry when the first physical value is three, using the
actual selected value and nonempty following register file. Under the stated
marker delimiter and k=1 controller layout, it reaches dense 42 and then takes
a data-dependent two-step branch:

- If the selected value is zero, the encoded returned run has the form
  `2*(2*q+1)` and the machine reaches dense 84 with the exact stated tape.
- If the selected value is a successor, the encoded returned run has the
  form `2*q+1` and the machine reaches dense 1 with the exact stated tape.

The model clock and all packed tape halves are explicit in Lean. The helper
`selectedFileCases` derives the required file shapes from the actual following
file rather than assuming an arbitrary delimiter is nonzero. These theorems
hold in every candidate PRA model, including for nonstandard values and
clocks. The split concerns only the first non-first marker position; other
positions and later paths from dense 84 or dense 1 remain separate.

These are conditional physical executions from the stated intermediate
marker layout. They do not establish blank-tape reachability, identify the
controls with source branches or frames, prove source-instruction simulation,
or prove an iPRA consistency implication.

The four new modules passed an author suffix rebuild against previously
checked prerequisite overlays, with `propext`, `Classical.choice`, and
`Quot.sound` as their reported axioms and no `sorryAx`. The full nested
checker `check-first-three-first-split.sh` is supplied but has not been run.
