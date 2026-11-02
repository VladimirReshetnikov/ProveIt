# Compact44 controller choice: exploratory specialization

`ArithmeticControllerChoiceCompact44.lean` mechanically adapts the existing
2011 controller-choice proof to block width `590069` and auxiliary modulus
`581197`, including the two corresponding oddness witnesses. It imports the
[compact controller-data prototype](../compact44-controller-data-prototype/README.md).
A single-side exploratory build exited 0 with the two linter warnings recorded
in `observation.txt`. The source states, in an IΣ₁ model, a definable Boolean
controller choice and a rank-calibration corollary under their explicit size,
support and unit hypotheses.

The run rebuilt the data module, then the choice module, on an overlay of a
historical provider with its `Foundation` root removed so imports resolve from
the available package overlay. **This is a mixed-provider experiment:** a
successful elaboration does not establish compatibility of inherited transitive
objects. It is not a coherent paired replay or an independent verification.
The connection from these abstract dummy positions and coefficients to the
retained compact44 graph, the fixed K, the machine computation and an iPRA
endpoint remains open.
