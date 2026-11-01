# Thirty-five-variable degree-six candidate

This 145-operation graph substitutes `V²` for `squareVariable` in the
36-variable parent, removing its defining residual square and accumulation
gate. `generate.py` pins the parent and verifies the changed rows, liveness and
topological order. `verify_substitution.py` checks all 23 parent residuals as
exact sparse integer polynomials under the substitution, with the removed
residual becoming zero. The remaining 22 residuals have degree at most three,
and `verify_degree.py` checks exact degree six.

Unlike the four substitutions in the parent, `V²` is not positive for every
positive input. The intended zero-set argument would derive `V ≠ 0` from the
auxiliary residual: with `Q > 0` and `y² > 0`, its equation
`y² - Q*(y² - V²) - 1 = 0` is impossible if `V = 0`. This observation still
needs a formal model proof and does not make the substitution a valid positive
valuation map for arbitrary inputs.

**Open:** the 35-variable graph is not yet bound to a Lean literal; the required
zero-dependent positivity, model equivalence, native iPRA endpoint and guarded
replays remain to be proved. The 36-variable parent now has a matched native
endpoint on a historical provider. No minimality is claimed.
