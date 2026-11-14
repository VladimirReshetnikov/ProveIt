# First-value-two positive marker path to state 106

`markerFirstTwoPositiveTo106` in `PA194FirstTwoPositiveTo106.lean` continues
the first non-first marker trace for first register value two and a positive
selected value, through dense state 85 and a model-length one-run scan to
state 106. The theorem gives exact tape halves and a model-valued clock in
any candidate-PRA model. It assumes the intermediate marker layout but does
not require a blank tail for this segment.

Both modules were compiled with previously checked prerequisite objects; their
printed theorem axioms contain no `sorryAx`. The nested replay wrapper was
syntax checked but not run for this change. The return beyond state 106,
blank-start reachability, and the source-frame correspondence remain open.
