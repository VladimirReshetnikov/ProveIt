# Forty-three-variable quartic candidate

This graph replaces the 44-variable parent's signed pair for the main root
`D` by one positive coordinate. It has 43 unknowns and 175 live operations.
`generate.py` pins the parent and checks gate bindings and liveness;
`verify_degree.py` checks all 33 residuals remain quadratic and their sum has
exact degree four. `verify_substitution.py` checks all 33 parent residuals
under the forward embedding `(dPositive,dNegative)=(D+1,1)`.

The proposed reverse implication requires `D>0` at a positive parent zero.
For a natural first port `beta≥2`, the residuals give `q=1+beta*J≥3`,
`phi=Y*q²`, `c=eta+Y*k≥Y*k`, `a=lambda+Y≥1`,
`H=3+4*a`, and `P=X+a*c`. Thus `phi*P≥phi*a*c>H*k`, while the main
root equation gives `D+H*k=phi*P+H*(S+x+epsilon+1)`. A generic IΣ₁-model
proof of the key inequality is checked exploratorily in
`/tmp/Z43InequalityProbe.lean`; the proof still needs to bind these
hypotheses to the exact candidate residuals and the fixed integer ports.

**Open:** no Lean literal binding, complete model equivalence, native iPRA
endpoint or guarded replay has yet been established for this candidate. The
natural-port and `beta≥2` hypotheses must be discharged explicitly for the
fixed instance. No global minimality is claimed.
