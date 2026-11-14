# Model-length state-16 return scan

`PA194SixteenReturnRun.modelSixteenReturnRun` gives an exact physical-table
transition from dense state 16 to 17 for an arbitrary model-valued unary-run
length. It is proved in every candidate-PRA model by composing the existing
state-17 marker-return cell with the one-step entry to state 16.

`PA194HalfFileSixExact.scanSixExact` strengthens the six-block forward scan:
it exposes the final left tape as a unary run over an even suffix, together
with the remaining-file relation. These results are intended to support the
return from the first-value-two positive marker path. They do not yet compose
that entire return to state 24 or connect it to blank-start execution.

Lean compiled both modules against retained prerequisite objects, with no
`sorryAx` in the printed theorem axioms. The nested replay wrapper was syntax
checked but not run for these modules.
