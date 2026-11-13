# Five-norm sharing-aware quartic seed candidate: 38 witnesses

This is an **external candidate**, not a Lean model bridge or new iPRA endpoint. The pinned source is the maintained current2011 14-positive-variable 65-gate graph. The candidate inlines 36 of the first 60 gates, materializes 19 signed-pair gates using 24 natural coordinates, and asserts five norm conditions directly instead of evaluating the last five product rows. Together with the fourteen shifted source inputs this gives **38 natural witnesses plus the unused distinguished Jones input**. There are 29 residuals: 24 materialized-pair equations and five norm equations. Each is of witness degree at most two, so the external sum of squares has degree at most four.

The terminal constraints, using the graph's actual names, are

```
N0 = 1,  N1 = 1,  Na = 1,  Nt = 1,  scaled_Ns = Delta.
```

They correspond to `P=1`, `Q=1`, `U=1`, `W=1`, and `strong=1`: the exact polynomial identity is `scaled_Ns = Delta * strong`, where `strong = f² − Delta*(i*c²)²`. `ModelCarrierSpheres.value65_zero_iff_norms` provides the relevant existing all-model norm theorem in a commutative, linearly ordered ring satisfying its `Facts` (including discreteness, the mod-4 map and near-square fact), with positive `p 0` and all fourteen source coordinates positive. `ModelCarrierScaled.delta_pos` supplies `Delta>0`; in that domain `scaled_Ns=Delta` is equivalent to `strong=1`. The candidate has **not** yet instantiated or recompiled that Lean bridge.

All four current fixed ports are checked positive. For the signed-pair witness construction in an arbitrary model, their ring values must be represented by nonnegative model naturals; this is additional to the norm theorem's explicit positive-beta hypothesis and is satisfied by the intended fixed natural ports if the relevant model-cast lemmas are supplied. The candidate uses coordinate `j+1` plus one for source coordinate `j`. The distinguished coordinate 0 is unused. At zero witnesses the first residual is exactly `−(beta+1)^2`, so the seed is nonzero for any distinguished input at positive beta.

`check.py` checks all 60 used graph rows against the recorded signed-pair identities, nonnegative pair components, 19 explicit cut names, every residual, coordinate uniqueness and liveness, all fixed-port bytes, the exact `Z=Delta*strong` identity, and the first-residual normalization. It also independently compares the original graph with the checked Lean source modulo associativity and commutativity and tests eight finite witness assignments against the five explicit norm squares. These checks do not replace an all-IΣ₁-model proof. The companion [bounded search](../nine-sharing-quartic65-norm-search/result.json) found these cuts but proves no minimality.

A completed Lean result still needs an `Expr` transcription and checked degree/normalization, a two-way model proof reconstructing these signed pairs and identifying their norm residuals with the actual `Carrier65.core` factors, the positive port casts and `Delta` cancellation, and a `NineFreshJones.nine_iff` instantiation followed by the existing consistency bridge. No final nine-variable operation count, degree, file/PDF theorem, or iPRA endpoint is claimed. Run `python3 -I -S -B check.py` from this directory; `build.py` pins its source and refuses to overwrite `seed.json`.
