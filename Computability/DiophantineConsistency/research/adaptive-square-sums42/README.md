# Forty-two-variable degree-6 candidate

This exploratory 164-operation circuit adds seven positive names and one
signed name represented by two positive variables to the 33-variable,
degree-8 circuit. The names stand for `q^2`, `X*Y`, `psi^2`,
`ell*(ell+k)`, `varphi^2`, `n*g`, `upsilon^2`, and the signed expression `Q`.
Eight squared constraints bind them to their old expressions. The graph is a
sum of 28 squares.

`generate.py` deterministically constructs the graph from the pinned parent
and checks that all gates, unknowns and ports are live. `verify_degree.py`
expands the 28 residual polynomials exactly, checks the final added-square
wiring, and finds maximum residual degree 3. One leading monomial has
port-independent coefficient −1, so the degree of the sum is exactly 6,
including after the positive-variable shift. These finite checks are not Lean
degree theorems.

**Open:** the graph has not yet been bound to a Lean literal and no
positive-zero equivalence, native iPRA endpoint, or proof replay has been
established. In particular, this candidate is not yet an equation claimed to
be equivalent to `Con(ZFC)`. No global minimality claim is made.
