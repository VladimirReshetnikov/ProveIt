# Sixteen-variable degree-24 main-scale witness

Starting from the fifteen-variable degree-26 equation, introduce a positive
coordinate `mainScaleVariable` for `U=Yq²`. Use it in the main residual and add
`(mainScaleVariable−U)²` as a seventh squared residual. The graph has 16
positive variables and 96 live unshifted binary operations. Its seven residual
degrees are 10, 12, 8, 10, 12, 4 and 3. The two degree-12 residuals contribute
the highest homogeneous part of the output as a sum of squares. The fifth has
an explicit degree-12 monomial with coefficient `−beta^8`, nonzero at the
actual positive beta. A nonzero sum of squares of real polynomials cannot
vanish identically, so the output has exact degree **24**, even after fixing
the ports and applying the positive shift. `verify_degree.py` checks the
sparse residuals and the leading witness. This is an integer-polynomial
certificate, not a Lean degree theorem or a minimality claim.

`AdaptiveMainScaleWitness16` binds the 96-gate literal by definitional equality
to a one-hole version of the fifteen-variable equation plus the new squared
constraint. In every IΣ₁ model, a zero projects to a parent zero and a positive
parent zero extends using the positive value `Yq²`. Its `current_no_zero_iff`
gives the exact shifted no-zero equivalence at the fixed ports; the general
transfer explicitly assumes positivity of the first port. `verify_literal.py`
compares every variable alias, port and literal gate against the pinned graph.
Normal Python and `python -O` pass.

Two focused [Lean model replays](../../reviews/adaptive-square-sums16-model-replay/README.md)
match on the same historical fifteen-variable provider. Transitive project,
package and dynamic ancestry remains inherited. The native iPRA endpoint for
this new expression is separate work and is not established by the model
receipt.

The separate [equation24.tex](../../equation24.tex) and
[equation24.pdf](../../equation24.pdf) show all 16 distinct positive unknowns,
seven squared residuals, the full base-10 fixed integer and 96 gates.
`verify_display24.py` parses all 27 displayed definitions and circuit rows,
checks the sum wiring and copied constants, and rejects two formula mutations;
it is a limited TeX parser. Normal Python and `python -O` pass. Two `pdflatex`
runs produced identical PDF SHA-256
`5e4ae926ca982f4a2e74a656a356bc3513d1161257857bdb1bf86f51229b46b4`;
both pages were visually inspected. The page states the model proof and the
pending native-iPRA endpoint separately.
