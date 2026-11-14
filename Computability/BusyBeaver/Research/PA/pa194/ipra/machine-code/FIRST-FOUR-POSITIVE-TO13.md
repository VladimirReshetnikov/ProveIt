# First-value-four positive marker return through state 13

`PA194FirstFourPositiveTo13.lean` continues the conditional physical-table
path for the first non-first marker. When the first register value is four,
the selected value is positive, the stated marker layout holds, and the fixed
finite remaining file has a blank tail, `markerFirstFourPositiveBlankTo13`
reaches dense control state 13 in every candidate-PRA model. Its model-valued
register lengths and time can be nonstandard.

`selectedZero` and `selectedSucc` give separate exact state-13 tape shapes.
The zero case consumes the first returned file block; the successor case
consumes the remaining selected block. `returnIsBlock` supplies the required
file shape. The final composition retains existential final tape halves; the
separate lemmas retain the explicit forms needed for further work.

The module was compiled against previously checked prerequisite objects; its
reported axioms do not include `sorryAx`. The nested wrapper provides a fresh
replay of its module chain but was not run for this change. This conditional
path does not establish blank-tape reachability, a source-frame simulation, or
either consistency implication for the literal 194-state machine.
