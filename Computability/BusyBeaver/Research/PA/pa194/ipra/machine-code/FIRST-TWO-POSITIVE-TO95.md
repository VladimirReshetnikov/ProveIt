# First-value-two positive marker path to state 95

`markerFirstTwoPositiveBlankTo95` in `PA194FirstTwoPositiveTo95.lean`
continues the first non-first marker trace from dense state 71 to 95. It
assumes first register value two, a positive selected value, the explicit
intermediate marker layout, and a blank tail after the finite remaining
file. The theorem covers arbitrary candidate-PRA models, including
nonstandard register values and run times; the final time and tape halves
are existential.

The strengthened state-71 theorem retains the relation between its right
half and the remaining file. `state71FileTo95` uses that relation to handle
both an empty and a nonempty remaining file, scanning a model-length unary
run in the nonempty case. Lean compiled the updated state-71 and new state-95
modules against previously checked prerequisites, with no `sorryAx` in the
printed theorem axioms. The nested replay wrapper was syntax checked but not
run for this module. Continuing the physical return and linking the trace to
the blank-start machine and source scheduler remain open.
