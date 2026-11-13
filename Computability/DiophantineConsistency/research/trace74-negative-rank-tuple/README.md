# Negative-rank update of the actual chart tuple

`Trace74NegativeRankTuple.updated_carrier` takes an arbitrary 74 chart
tuple over a commutative ring and updates its `F` and `C` coordinates to

```
F = 1,   C = q*h + N,   h = p₀v₀,   q = h+1.
```

The updated chart has rank `R=RJ−(q²−1)N`. The theorem applies the
checked carrier chart binding to this same tuple: it assumes the two
corresponding CRT divisibilities `h ∣ (p₁+v₅)C−1` and `XY ∣ k−R−1`, and
the unchanged Pell-carrier divisibility `H ∣ K`; it concludes the
actual updated chart satisfies `M ∣ Z`.

This theorem does not itself construct `N`, prove the Bézout certificates,
or tie the model's natural witnesses and casted ports to a particular
fixed tuple. The Pell-carrier divisibility is also still an assumption;
see the separate [Pell congruence result](../trace74-carrier-pell-congruence/README.md).

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and the previously built dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-negative-rank-tuple Computability/DiophantineConsistency/research/trace74-negative-rank-tuple/Trace74NegativeRankTuple.lean -o /tmp/Trace74NegativeRankTuple.olean
```

`#print axioms` reports `[propext, Quot.sound]`. SHA-256 hashes:

```
e954bd6680f2d2ae09723d3f0b4e2cd8980e66783d594ae90ac35c149d020922  Trace74NegativeRankTuple.lean
bc83c2cc9a3ac1f94a41aca6e27ec921a4856ee358a92191130e89864df082b5  Trace74NegativeRankTuple.olean
dde3d30a37241c7e9a15ac6f4128750106dc24a1160a086e8f504bebe2caaa78  Trace74CarrierChartBinding.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
