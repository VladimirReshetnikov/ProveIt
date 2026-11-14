# First-value-two positive marker path to state 17

`markerFirstTwoPositiveBlankTo17` in `PA194FirstTwoPositiveTo17.lean`
continues the first non-first marker path from dense state 16 to 17. It
assumes first register value two, a positive selected value, the explicit
fixed eight-block marker layout, and a blank tail. It holds in arbitrary
candidate-PRA models, including nonstandard values and times.

The state-14 intermediate theorem now retains the final unary-run structure;
the state-16 theorem carries it to the existing model-length return scan.
The final state-17 theorem records existential tape halves and time. Lean
compiled both new modules against retained prerequisite objects, and the
printed theorem axioms contain no `sorryAx`. The nested replay wrapper was
syntax checked but not run for these modules.

Further file structure is needed to continue the physical return to state 24.
Blank-start reachability, the source-frame correspondence, and both iPRA
consistency directions for the literal machine remain open.
