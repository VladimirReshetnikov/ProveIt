# Forty-four-variable quartic candidate

This graph replaces both signed positive-coordinate pairs for `W` and the root
skew `Γ` in the 46-variable oriented-root parent by single positive variables.
The pinned circuit has 44 unknowns and 176 live operations. `generate.py`
checks the replaced parent gates and graph liveness; `verify_degree.py` checks
that all 33 residuals are quadratic and their sum has exact degree four.
`verify_substitution.py` checks all parent residuals under the forward
embedding `(wPositive,wNegative)=(W+1,1)` and
`(rootSkewPositive,rootSkewNegative)=(Γ+1,1)`.

The reverse direction needs positivity of the original signed `W` at every
positive parent zero. The proposed argument uses its first norm: if `W≤0`,
the root-skew constraint gives `Γ=kW`, and the root equation forces the
positive first root to be at least `psi*(ell+k)`. Its norm and the positive
scale instead give `Z=psi*t` with `t<ell+k`. The general IΣ₁ inequality
`ArithmeticAdaptiveTransport2011.first_root_bound` supplies the last bound,
but the required residual extraction and model witness map are not yet
proved for this candidate. The fixed first port is positive; any broader port
assumptions must remain explicit.

**Open:** the 44-variable graph is not yet bound to a Lean literal; the
signed-W positivity, model equivalence, native iPRA endpoint and guarded
replays remain to be proved. No global minimality is claimed.
