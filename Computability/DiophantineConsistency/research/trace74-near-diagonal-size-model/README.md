# Uniform lower power bound for near-diagonal indices

`Trace74NearDiagonalSizeModel.lower_power_bound` proves, over any model of `IΣ₁`,

```text
512 h² K⁴ < power Y (d+2),
```

from the explicit hypotheses `q ≥ 1073741824`, `q² ≤ Y`, `h < q`, `r ≤ d+10`, and `K = power 2 r`. The model's represented exponentiation is used throughout. For a graph application with `n≥8`, take `d=n−8`, so the exponent is `n−6` and the index condition is `r≤n+2`.

The argument uses `P=power 2 d`, then `Y≥16` gives `P⁴≤power Y d`, and `r≤d+10` gives `K≤1024P`. The fixed comparison `q²>2⁴⁹`, together with `h<q` and `Y≥q²`, yields `2⁴⁹h²<Y²`; multiplying by `P⁴` and comparing `K⁴` establishes the result. This is a model-indexed theorem; it does not itself establish the numerical or index hypotheses from a graph zero. In particular the near-diagonal index condition remains a premise, and no reverse guard or iPRA endpoint follows from this theorem alone.

A captured-provider author check exited 0 and reported `[propext, Classical.choice, Quot.sound]`:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-near-diagonal-size-model \
  Computability/DiophantineConsistency/research/trace74-near-diagonal-size-model/Trace74NearDiagonalSizeModel.lean \
  -o /tmp/Trace74NearDiagonalSizeModel.olean
```

SHA-256: source `e362e69a8b5ae9b23a7a8c89ae03b70934db1e421044daf52a9576159fc972a6`, direct imported `Trace74NearDiagonalLargeHeightModel.olean` `01b02431bd9afe6f85c07190976b120c27519310807e2936a0282ba5a7b96252`, output object `dd4398cd1513c2e05fdca415c8fa76a75c4d40862fe2d7a5db3047df054f1513`. Two earlier attempts failed on tactic cleanup; the documented command is the successful third author check. Temporary providers and their transitive dependencies and search-path resolution have not been independently audited; this is not a clean current-source rebuild or independent replay.
