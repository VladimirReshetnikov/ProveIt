# Candidate: 30 variables, degree eight, 138 circuit operations

The [base-10 display](../../equation8-30.pdf) is an **unproved candidate**, not a new ZFC-consistency equivalence.
It eliminates the positive named W coordinate from the pinned 31-variable
equation by substituting its defining expression `Bt = C*(X + K*q) - F*q`
throughout the graph and removing the now-zero W defining residual. The result
has 30 positive inputs, four fixed ports, 21 squared residuals and 138 live
arithmetic rows.

`verify_substitution.py` checks by exact polynomial arithmetic that all 22
parent residuals agree after the substitution, with the eliminated residual
identically zero. This finite identity alone is not a Lean zero-set theorem: the
candidate-to-parent witness map additionally needs the computed W value to be
strictly positive. That positivity and the shifted no-zero equivalence with
the 31-variable equation are now proved in every IΣ₁ model for natural port
vectors, with a [matched focused model replay](../../research/adaptive-aq30-proof/README.md).
The native endpoint replay is still in progress, so the candidate remains
unproved as a native iPRA consistency equation.

`verify_degree.py` checks exact degree eight after the positive shift using
sparse integer polynomials. A maximum-degree residual has a nonzero
port-independent highest-degree monomial; the sum of its square and the
other squared residuals cannot cancel the leading degree over the reals. This
is a finite computation, not a Lean degree theorem. No minimum is claimed.

Run `python generate.py` and then `python verify_substitution.py`; all scripts
pin their graph inputs. Candidate SHA-256:
`f6c88de69011dc070c3cb642cf12bc27bb20c6ee92eaabb56dc1ccd884f685ad`.
