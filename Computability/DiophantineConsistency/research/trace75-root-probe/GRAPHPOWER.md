# Trace75 exact rank power

`Trace75GraphPower.graph_power` proves `X=2^rankNat` in every IΣ₁ model
with β≥31, `MC<β`, `MF<2β`, and an actual positive trace75 zero. `K0` is
arbitrary. It combines one variable-height witness `r` with the rank window,
the weighted whole-product divisibility, the extra-factor product estimate,
and the generic small-divisibility theorem. It derives `X≥32`, `r≥20`,
and `h*X≤X²`. The entire factor `h*X` remains present until positivity
and the strict whole-product magnitude force the product to zero; no
coprimality or modular cancellation of `X` is assumed.

This is a necessary condition on positive trace75 zeros. It is not a
halting or iPRA equivalence and does not remove the guard from trace74.

Accepted `run-graphpower-v2.py`, `observations/graphpower-attempt02/`: Lean
exit 0, no warning/error; object
`/tmp/trace75-graphpower-p_cl8tfn/Trace75GraphPower.olean`, SHA-256
`5704c79a5e8a267190a59ac245282eb119c7e3ea039d43cbc4b55dde1802d9a9`.
Attempt 01 is retained: elaboration failed on an untyped intermediate
inequality and reported `sorryAx`. Selected direct providers are pinned;
historical transitive/package ancestry and external graph/file binding remain
inherited limits.

The same source also passed `run-graphpower-v3.py`,
`observations/graphpower-attempt03/`, producing a byte-identical object at
`/tmp/trace75-graphpower-2136o7kc/Trace75GraphPower.olean`. This run pins
the first-selected `ModelRatioBounds.olean` at the variable-height overlay,
SHA-256 `fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7`.
It resolves to a historical provider with known producer-time drift. Pinning
that same object improves this run's evidence; a coherent rebuild against
the separately audited fresh provider remains needed.
