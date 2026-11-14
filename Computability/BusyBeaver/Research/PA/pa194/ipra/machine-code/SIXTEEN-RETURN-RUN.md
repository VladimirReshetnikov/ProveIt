# Model-length state-16 return scan

`PA194SixteenReturnRun.modelSixteenReturnRun` gives an exact physical-table
transition from dense state 16 to 17 for an arbitrary model-valued unary-run
length. It is proved in every candidate-PRA model by composing the existing
state-17 marker-return cell with the one-step entry to state 16.

`PA194HalfFileSixExact.scanSixExact` strengthens the six-block forward scan:
it exposes the final left tape as a unary run over an even suffix, together
with the remaining-file relation. These results are intended to support the
return from the first-value-two positive marker path. The later
[state-24 theorem](FIRST-TWO-POSITIVE-TO24.md) completes that conditional
return; blank-start reachability remains open.

Lean compiled both modules against retained prerequisite objects, with no
`sorryAx` in the printed theorem axioms.

A full nested `check-first-two-positive-two-returns.sh` replay also passed
with no `sorryAx`, rebuilding its machine-code chain against retained
prerequisite overlays.
