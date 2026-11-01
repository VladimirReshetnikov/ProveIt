# Forty-two-variable degree-6 candidate

[equation6.pdf](../../equation6.pdf) presents this circuit and its fixed
constants in base 10. `generate_equation6.py` constructs the TeX from the
pinned graph; `verify_display6.py` checks all displayed definitions, 164 gates,
fixed constants and two mutation controls. Two `pdflatex` runs produced the
same PDF SHA-256
`dcb586dbfe29260a405038f4c941997d9599fada24b992b8e58926d302251fc1`;
both pages were inspected.

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

`verify_literal.py` matches the actual Lean literal and all 164 gate rows to
the pinned candidate. `AdaptiveNamedValues42.shifted_no_zero_iff` proves both
positive-zero directions in every IΣ₁ model for natural ports;
`current_no_zero_iff` specializes to the actual fixed ports. The [paired
model replay](../../reviews/adaptive-square-sums42-model-replay/README.md)
matched on a historical provider.

The [native iPRA endpoint](../../Lean/DiophantineConsistency/IPRANamedValues42Native.lean) has a matching [guarded replay](../../reviews/ipra-named42-native-verification/README.md) on a historical provider. It uses the chosen mapped ZFC-refutation predicate; the shared project, package, and dynamic-import ancestry remains inherited. No global minimality claim is made.
