# Closing an equality atom in both polarities

`PA194CloseEquality.lean` constructs an explicit four-argument primitive-
recursive code for closing a free-variable label in the two slots of an
equality atom. The input is the label, the two variable indices, and the
current binder depth. Its output is a bare pair of the positive and negative
NNF equality-formula codes with the selected variables replaced by a bound
variable at that depth.

`modelCloseEqDual` proves the exact numeric equation in every candidate-PRA
model, including nonstandard labels and depths and all cases where labels
coincide. `modelCloseEqDualQuote` separately identifies the output with
Foundation's quotes of the actual lifted `closeLabel` rewriting and its
negation for standard labels and depths, under an explicit IΣ₁ assumption.

This covers equality atoms made from two source variables, not arbitrary terms
or formulas. It does not provide the generic recursive closing operation used
by the dual translator, prove the source translation's global polarity
invariant, or establish PA calibration or a machine-consistency implication.
Rebuild with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-close-equality.sh
```
