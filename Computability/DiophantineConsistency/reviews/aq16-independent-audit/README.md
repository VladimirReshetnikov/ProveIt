# Independent finite audit of the AQ16 reduction

`audit.py` independently checks the recorded AQ17 and AQ16 graph bytes, all
16 distinct inputs, four ports, 96 live operations, and both output
sum-of-squares trees. It checks the seven retained residuals by structural
substitution and the deleted residual by its exact binding. It independently
expands the signed positivity identity using sparse polynomials with sorted
index tuples. The graph shapes give `q >= 3`, `a >= 2`, and
`U*a*Y >= 9*a > 4*a+3 = H` for positive witnesses and `beta >= 2`; hence all
three displayed terms in the candidate's positivity decomposition are
positive. This uses integer subtraction, not truncated subtraction.

The audit checks exact degrees of all residuals and verifies that the degree-16
residual `A0` has coefficient `-beta^8` at the witness monomial
`J^8 X^2 Y^4 eta^2`. The recorded beta bytes equal `2^94517 - 1`, so the
leading sum of squares is nonzero after fixing the ports and the equation has
degree exactly 32. Wrong-sign positivity, retained-residual wiring, deleted
binding and output-sign mutations are rejected. The prior AQ17 independent
audit supplies the antecedent finite equivalence, not an AQ16 Lean theorem.

An ordinary invocation of `audit.py` exited 0; the corresponding `python3 -O`
invocation exited 1 because optimized Python is deliberately unsupported.
The exact commands, observed output and exit codes are recorded in
`terminal-observation.json`. The beta-to-Lean and displayed-constant links
inherit the historical parent and manually transcribed TeX recipe boundaries.
This is finite external reasoning, not a guarded Lean replay, a theorem about
PDF semantics, or a minimality result.
