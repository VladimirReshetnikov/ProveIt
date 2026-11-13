# Sign23 Delta coordinate, attempt 01: failure

The author observed numeric outer session `90674` exit 1. Dependency
inspection succeeded, but Lean compilation exited 1 with an unsolved
`delta_zero` goal: the numeral embeddings `ι 4` and `ι 3` were not simplified
to the corresponding difference-ring numerals. The failed `delta_zero` axiom
report includes `sorryAx`; it is not a proved theorem. The later printed
`delta_coordinate` and `lift_drop` axiom reports do not list `sorryAx`, but
the stage as a whole failed, no object was produced and no final postflight
ran. There is also one unused-variable warning.

The terminal state, logs and author-observed numeric outer exit are frozen
here. Independent failure audit requested. Any retry must use a fresh packet
and output path, with the numeral rewrite separately reviewed.
