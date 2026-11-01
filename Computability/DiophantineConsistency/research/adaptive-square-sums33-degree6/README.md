# Thirty-three-variable degree-six positive-transport candidate

This 143-operation graph replaces the signed `W` pair in the 34-variable
degree-six candidate with a single positive coordinate. `generate.py` pins the
parent and checks the changed rows, liveness and gate order.
`verify_substitution.py` checks all 22 parent residuals under the positive
embedding `wPositive = wValueVariable + 1`, `wNegative = 1` as exact sparse
polynomials. `verify_degree.py` checks that the residuals have degree at most
three and their sum of squares has exact degree six.

The reverse direction would require showing that signed `W` is positive at a
parent zero. The existing `ArithmeticAdaptiveTransport2011.first_root_bound`
and `quotients_force_transport` suggest a route through the first Pell norm,
positive scale and fixed positive first port. Their hypotheses have not yet
been bound to this literal in Lean. The 34-variable parent also has an open
model proof. These finite checks alone do not establish zero-set equivalence.

**Open:** no Lean literal binding, model equivalence, native iPRA endpoint or
guarded replay has yet been established for this candidate. No global
minimality is claimed.
