# Exact root-binding factorization: 17/94/20

This source-only graph has 17 positive inputs, 94 binary operations and
degree 20; the literal natural shift has 17 inputs, 111 operations and
the same degree. It is **exactly the same polynomial for all integer inputs and
ports** as the pinned [17-input parent](../adaptive-aq17-positive-bindings95/), whose degree certificate
and zero-map assumptions therefore apply. This is a gate-count improvement,
not a claim of global minimality or a new Lean endpoint.

The parent defines `M = q3*qm` and uses it only in `M*firstDelta`. Its root
binding is

```
M*firstDelta - Y*qm + Bt*q3
  = q3*(qm*firstDelta + Bt) - Y*qm.
```

Replacing the former by the latter deletes the separate `M` multiplication
and saves one operation after accounting for all changed nodes. The checker
matches every remaining residual as an exact sparse polynomial over arbitrary
integer ports, confirms that each output is the same sum of squared residuals,
and checks source topology, liveness, both graph counts and the literal natural
shift. Exact degree is inherited from the parent's separately checked leading
monomial; this identity cannot change it.

The parent's mathematical zero-set chain retains its stated hypotheses and
source provenance. **This new syntax and its endpoint have not been elaborated
in Lean**, and the finite checker does not supply a derivation in iPRA.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/adaptive-aq17-factored-root94/build.py
python3 -I -S -B research/adaptive-aq17-factored-root94/check.py
```

The deterministic checker output is [receipt.json](receipt.json). No Lean
process is run.
