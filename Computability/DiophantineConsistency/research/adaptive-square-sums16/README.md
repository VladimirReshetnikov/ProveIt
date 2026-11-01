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
package and dynamic ancestry remains inherited. The exact literal also has a native iPRA endpoint:
`IPRAMainScaleWitness16Native.literal_equivalence` asserts a derivation of the
no-positive-zero/selected ZFC consistency equivalence in the explicitly
defined native theory. The [two guarded comparisons](../../reviews/ipra-main16-native-verification/README.md)
match all twelve compiled suffix modules and 11,495 guarded files. This is a
fixed-source result on the inherited historical provider, not a full
source-current closure; package-transitive and dynamically loaded ancestry
remain inherited.

The separate [equation24.tex](../../equation24.tex) and
[equation24.pdf](../../equation24.pdf) show all 16 distinct positive unknowns,
seven squared residuals, the full base-10 fixed integer and 96 gates.
`verify_display24.py` parses all 27 displayed definitions and circuit rows,
checks the sum wiring and copied constants, and rejects two formula mutations;
it is a limited TeX parser. Normal Python and `python -O` pass. Two `pdflatex`
runs produced identical PDF SHA-256
`9a54daae6adb2027ea3086b5da62cceaa3ebc22ff40498943e78a82c59079356`;
both pages were visually inspected. The page states the matched native-iPRA result and its snapshot boundary.
