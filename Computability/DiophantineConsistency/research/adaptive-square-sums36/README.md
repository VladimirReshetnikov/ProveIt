# Thirty-six-variable degree-six candidate

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

**Open:** the 36-variable graph is not yet bound to a Lean literal; its model
equivalence, native iPRA endpoint and guarded replays remain to be established.
The parent 40-variable proof also remains open. No minimality is claimed.
