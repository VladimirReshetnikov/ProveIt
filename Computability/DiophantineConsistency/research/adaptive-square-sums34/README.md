# Thirty-four-variable degree-six orientation candidate

This 144-operation graph replaces the signed `Z` pair in the 35-variable
parent by one positive coordinate. `generate.py` pins the parent and checks
the changed rows, liveness and gate order. `verify_degree.py` checks that the
22 residuals have degree at most three and that their sum of squares has exact
degree six. `verify_substitution.py` checks all parent residuals under the
positive embedding, while `verify_orientation.py` checks the exact polynomial
identity for the proposed negative-root orientation.

The reverse argument would use the first residual to derive `|Z| = psi*t > 0`
for a natural `t`, then replace negative `Z` by `|Z|` while increasing the
positive `r` coordinate by `2*t`. This is the same orientation idea as the
[46-variable quartic candidate](../adaptive-square-sums46/README.md); the
first residual here already contains `psi²` directly. The polynomial checks
do not prove the required quotient or model transport. The 35-variable parent
now has a matched native endpoint on a historical provider.

**Open:** no Lean literal binding, all-model equivalence, native iPRA endpoint
or guarded replay has yet been established for this candidate. No global
minimality is claimed.
