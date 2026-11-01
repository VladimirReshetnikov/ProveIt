# Fifty-one-variable degree-4 candidate

This exploratory 187-operation circuit extends the 42-variable degree-6
candidate with five positive names and two signed names represented by four
positive coordinates. The seven names stand for `delta*n`, the rank seed,
`Y*k`, `k*W`, `X+a*c`, `varphi*gamma`, and `T*c`. Seven squared constraints
bind them to their old expressions. The graph is a sum of 35 squares.

`generate.py` deterministically builds the graph from the pinned parent and
checks liveness. `verify_degree.py` expands all 35 residual polynomials,
checks the newly added square-sum wiring, and finds all residuals have degree
at most two in the 51 unknowns. One degree-two residual contains a monomial
with port-independent coefficient 1. Its sum of squares therefore has exact
degree 4, including after positive-variable shifting. These finite Python
checks are not Lean degree theorems.

`verify_literal.py` matches the actual Lean literal and all 187 gate rows to
the pinned graph. `AdaptiveNamedValues51.shifted_no_zero_iff` proves both
positive-zero directions in every IΣ₁ model, for every integer port vector.
The [paired model replay](../../reviews/adaptive-square-sums51-model-replay/README.md)
matched on a historical provider.

**Open:** the native iPRA endpoint and its guarded replay remain separate
work. These checks inherit historical project, package-transitive and dynamic
ancestry. No global minimality claim is made.
