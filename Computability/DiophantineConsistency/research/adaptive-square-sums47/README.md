# Forty-seven-variable quartic candidate

This 179-operation graph substitutes the linear expressions
`eta + ySumVariable` and `productVariable2 + Y` for the 49-variable parent’s
`cVariable` and `aVariable`. Both expressions are positive when the remaining
unknowns are positive. It removes the two corresponding squared residuals and
their accumulation gates. The remaining 33 residuals are quadratic, so the
sum has exact degree four. `generate.py` pins the parent, verifies the changed
rows, and checks all inputs and gates are live and topologically ordered.

`verify_substitution.py` independently expands the residuals as exact sparse
integer polynomials, checking that every parent residual specializes to its
candidate counterpart and both omitted residuals become zero. `verify_literal.py`
checks all 47 variable declarations, four fixed ports and 179 gate rows against
the actual Lean literal. Degree and positive-shift checks remain finite
computations, not Lean degree theorems.

The Lean modules `AdaptiveNamedValues47Context`, `AdaptiveNamedValues47Maps`,
`AdaptiveNamedValues47Zeros`, and `AdaptiveNamedValues47Model` prove that the
candidate and 49-variable graph have equivalent no-zero statements in every
IΣ₁ model for arbitrary integer ports. The common residual context binds both
graphs by definitional equality; a finite fold of squares gives the necessary
zero criteria. In a 49-variable zero the deleted residuals determine both
coordinates, while the converse inserts the two positive sums. The module
`AdaptiveNamedValues47` composes this with the fixed-port 42-variable theorem.

`replay_model.py` produced matching author and peer replays of all seven
source modules on the same accepted 49-native parent, including a fresh build
of `AdaptiveFoldSquares`, with recorded exit and direct dependency/companion
guards in `reviews/adaptive-square-sums47-model-replay/`. This focused evidence
inherits historical project and package ancestry; it is not a current-source
closure. The native endpoint `IPRANamedValues47Native.literal_equivalence` has also
passed a separately matched nine-module replay, recorded under
`reviews/ipra-named47-native-verification/`. It proves equivalence to the
negation of the mapped native refutation predicate; the separate identification
of that predicate with ordinary Con(ZFC) is not established by this endpoint.
No global minimality is claimed.
