# Sign21 normalized-S coordinate, attempt 01

The author observed numeric outer session `1992` exit 0 and print
`PASS sign21 coordinate diagnostic`. The guarded stage passed; terminal
state, logs and hashes are frozen here. The row report lists `propext`, and
the other three reports list Lean metatheory axioms `propext`,
`Classical.choice` and `Quot.sound`, not iPRA axioms. One unused-variable
warning is reported; no `sorryAx` was found. Independent terminal audit
requested.

This checks the natural S lift, deleted row, coordinate recovery and lift
after drop. It does not check retained-row transfers, the assembled model
bridge, Lean/JSON binding, Lean degree or iPRA endpoint. Inherited provider
and point-observation qualifications remain.
