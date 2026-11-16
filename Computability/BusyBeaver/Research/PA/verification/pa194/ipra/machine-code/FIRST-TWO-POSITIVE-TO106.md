# First-value-two positive marker path to state 106

`markerFirstTwoPositiveTo106` in `PA194FirstTwoPositiveTo106.lean` continues
the first non-first marker trace for first register value two and a positive
selected value, through dense state 85 and a model-length one-run scan to
state 106. The theorem gives exact tape halves and a model-valued clock in
any candidate-PRA model. It assumes the intermediate marker layout but does
not require a blank tail for this segment.

Both modules were compiled with previously checked prerequisite objects; their
printed theorem axioms contain no `sorryAx`. The later [state-24 theorem](FIRST-TWO-POSITIVE-TO24.md) continues this
conditional path. Blank-start reachability and source-frame correspondence
remain open.

A full nested `check-first-two-positive-two-returns.sh` replay also passed
with no `sorryAx`, rebuilding its machine-code chain against retained
prerequisite overlays.
