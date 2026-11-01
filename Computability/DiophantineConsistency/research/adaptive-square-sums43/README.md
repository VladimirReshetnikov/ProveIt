# Forty-three-variable quartic candidate

This graph replaces the 44-variable parent's signed pair for the main root
`D` by one positive coordinate. It has 43 unknowns and 175 live operations.
`generate.py` pins the parent and checks gate bindings and liveness;
`verify_degree.py` checks all 33 residuals remain quadratic and their sum has
exact degree four. `verify_substitution.py` checks all 33 parent residuals
under the forward embedding `(dPositive,dNegative)=(D+1,1)`.

For a natural first port `beta≥2`, the residuals give `q=1+beta*J≥3`,
`phi=Y*q²`, `c=eta+Y*k≥Y*k`, `a=lambda+Y≥1`,
`H=3+4*a`, and `P=X+a*c`. Thus `phi*P≥phi*a*c>H*k`, while the main
root equation gives `D+H*k=phi*P+H*(S+x+epsilon+1)`. The Lean modules
`AdaptiveZ43Inequality` through `AdaptiveZ43Model` prove the required positivity
and no-zero equivalence for arbitrary natural ports satisfying `beta≥2` in
every IΣ₁ model. `AdaptiveZ43FixedPort` proves this bound for the fixed ports
and handles their casts; it does not assume positivity of unrelated ports.
`verify_literal.py` binds the 43 variable slots and 175 operations in Lean to
the pinned graph.

The [paired model replay](../../reviews/adaptive-square-sums43-model-replay/README.md)
checks nine modules twice on a shared fixed provider, with source/object/log and
direct dependency guards. It inherits the provider's transitive and dynamic
ancestry. The fixed-port native iPRA client has compiled exploratorily; its
guarded paired replay remains pending. No global minimality is claimed.
