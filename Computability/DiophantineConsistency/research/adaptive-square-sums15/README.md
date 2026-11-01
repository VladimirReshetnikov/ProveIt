# Fifteen-variable degree-26 scale-witness equation

Starting from the fourteen-variable, 90-operation direct-square candidate,
add one positive coordinate `scaleVariable` for the scale `M=q³(q−1)` in the
first residual. Replace both uses of `M` in that residual by the new coordinate
and add `(scaleVariable−M)²` as a sixth squared residual. The graph has 15
positive variables and 93 live unshifted binary operations. The six residual
degrees are 10, 13, 8, 10, 12 and 4. The main residual is the unique one whose
square has degree 26; a degree-13 monomial has nonzero coefficient `8*beta^4`
after the actual positive beta is fixed. `verify_degree.py` checks the sparse
polynomials and this exact-degree argument. The result is not a Lean theorem
about degree or a minimality claim.

`AdaptiveScaleWitness15` binds the literal by definitional equality to a
one-hole version of the 14-variable equation plus the scale constraint. In
every IΣ₁ model, any zero projects to a 14-variable zero. Conversely, a
positive parent zero extends by choosing the new coordinate as `q³(q−1)`,
which is positive under the fixed-port beta bound. `current_no_zero_iff` gives
the exact shifted no-zero equivalence at the fixed ports; the more general
transfer explicitly assumes positivity of the first port. `verify_literal.py`
compares all 15 variable aliases, four ports, and 93 Lean literal gates to the
pinned graph. Normal Python and `python -O` pass.

Two focused [Lean model replays](../../reviews/adaptive-square-sums15-model-replay/README.md)
match on the same historical parent. Transitive project, package and dynamic
ancestry is inherited. The native iPRA endpoint for this new expression is not
yet established by this receipt and remains separate work.
