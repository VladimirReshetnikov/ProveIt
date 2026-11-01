# Thirty-two-variable degree-six positive-main-root candidate

This 142-operation graph replaces the signed main-root `D` pair in the
33-variable degree-six candidate with one positive coordinate. `generate.py`
pins the parent and checks changed rows, liveness and gate order.
`verify_substitution.py` checks all 22 parent residuals under the positive
embedding `dPositive = dValueVariable + 1`, `dNegative = 1` as exact sparse
polynomials. `verify_degree.py` checks that the residuals have degree at most
three and the sum of squares has exact degree six.

The reverse direction would require proving signed `D` positive at a parent
zero. A proposed route uses the main-root residual, `q ≥ 3` from the fixed
first port, and the positive-input bounds on the named expressions. Those
inequalities have not yet been bound to this literal in Lean. The parent itself
still has an open native proof; the finite checks do not establish zero-set
equivalence.

**Open:** no Lean literal binding, model equivalence, native iPRA endpoint or
guarded replay has yet been established for this candidate. No global
minimality is claimed.
