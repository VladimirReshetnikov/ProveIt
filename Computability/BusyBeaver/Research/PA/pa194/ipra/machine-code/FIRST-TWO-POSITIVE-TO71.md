# First-value-two positive marker path to state 71

`markerFirstTwoPositiveBlankTo71` in `PA194FirstTwoPositiveTo71.lean` continues
the first non-first marker trace from dense state 106 to 71. It assumes first
register value two, a positive selected value, the explicit intermediate
marker layout, and a blank tail after the finite remaining file. It covers
arbitrary candidate-PRA models, including nonstandard register values and
run times; the final tape halves and time are existential.

The proof first shows that the remaining file code has even parity under the
blank-tail condition, then applies the existing state-106 scan. Lean compiled
the module against previously checked prerequisite objects with no `sorryAx`
in its printed theorem axioms. The nested replay wrapper was syntax checked
but not run for this module. Continuing to the next source frame and linking
the physical trace to blank-start execution remain open.
