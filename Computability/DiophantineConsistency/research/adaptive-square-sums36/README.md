# Thirty-six-variable degree-six equation

This 148-operation graph simultaneously substitutes four positive product
and square definitions into the 40-variable parent: `cubeVariable = q *
qSquareVariable`, `productVariable = productVariable2 * q`,
`psiSquareVariable = scaleVariable²`, and `ySquareVariable = y²`. The fixed
positive first port makes `q` positive for positive inputs; all four values
are therefore positive. Four squared residuals and their accumulation gates
are removed.

`generate.py` pins the parent, checks all replaced definitions and accumulation
rows, and verifies the new graph's liveness and topological order.
`verify_substitution.py` checks all 27 parent residuals as exact sparse integer
polynomials under the simultaneous substitution and verifies that the four
removed residuals vanish. The remaining 23 residuals have degree at most
three, with a nonzero cubic leading term; `verify_degree.py` therefore checks
exact degree six. These checks are finite computations, not Lean theorems.

The exact graph is bound to `AdaptiveAQ36Literal.literal`. The general
`AdaptiveAQ36.shifted_no_zero_iff` proves no-zero equivalence with the
40-variable parent in every IΣ₁ model when the first port is a nonnegative
integer; `current_no_zero_iff` discharges that condition at the fixed ports.
The [native endpoint](../../Lean/DiophantineConsistency/IPRAAQ36Native.lean)
has a [matched nine-module replay](../../reviews/adaptive-aq36-native-replay/README.md).
It uses the mapped Foundation refutation predicate; identification with
Con(ZFC) relies on the separate interpretation and refutation bridge. The
historical provider and inherited project, package-transitive and dynamic
ancestry remain qualifications. No minimality is claimed.

The [base-10 presentation](../../equation6-36.pdf) uses separately named
positive variables. `generate_equation6_36.py` produces the TeX and
`verify_display6_36.py` checks 44 definitions, 23 residuals, 148 circuit rows,
fixed constants and mutation controls. Two clean PDF builds matched SHA-256
`b63eb57ed20008e1b6667703e8ce557c8494a78b98596b1cd9490e87d676fc4e`.
