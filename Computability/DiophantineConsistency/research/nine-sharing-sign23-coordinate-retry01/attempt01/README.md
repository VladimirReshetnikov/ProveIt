# Sign23 Delta coordinate retry, attempt 01

The author observed numeric outer session `61340` exit 0 and print
`PASS sign23 coordinate numeral-rewrite retry`. The guarded stage passed;
its terminal state, logs and hashes are frozen here. The old-row report lists
`propext`, while the other three reports list Lean metatheory axioms
`propext`, `Classical.choice` and `Quot.sound`; these are not iPRA axioms.
One unused-variable warning remains. Independent terminal audit requested.

This checks the Delta lift, deleted row, coordinate recovery and lift after
drop. It does not check retained-row transfers, the assembled model bridge,
Lean/JSON binding, Lean degree or an iPRA endpoint. Provider and
point-observation qualifications remain.
