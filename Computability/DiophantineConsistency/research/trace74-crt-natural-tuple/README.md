# CRT construction on a natural chart tuple

`Trace74CRTNaturalTuple.exists_updated_carrier` combines the model-level
negative-rank CRT with the actual tuple update. In any IΣ₁ model, it
constructs an internal natural `N` larger than an arbitrary internal
bound, and sets

```
w = update (update v 1 1) 2 (q*h+N).
```

For the cast of this **same natural tuple** `w`, it proves the actual
74 chart's `M ∣ Z`. The updates preserve coordinates 5, 6, 8, and 9,
which contain the first Pell seed data. The source establishes the
equality between the cast of the natural update and the ring update
before applying the chart lemma.

The theorem assumes positive model parameters, six explicit difference-
ring Bézout certificates, parameter bindings to `p` and `v`, and the
unchanged `H ∣ K` carrier premise. The latter can follow from the
separate [Pell congruence theorem](../trace74-carrier-pell-congruence/README.md)
once its own premises are provided. None of those certificates or the
congruence is discharged here for the concrete graph. Carrier
divisibility alone does not establish graph zero, the carrier quotient,
the adjacent Pell norm, or an iPRA proof.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and the previously built dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-crt-natural-tuple Computability/DiophantineConsistency/research/trace74-crt-natural-tuple/Trace74CRTNaturalTuple.lean -o /tmp/Trace74CRTNaturalTuple.olean
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
SHA-256 hashes for that run:

```
8df9597208cc079dae7022c2334d5fbfc8ea8d0a31d5064b94e5b5c54687efda  Trace74CRTNaturalTuple.lean
179954bfa22feb2c54af4d56f86e8276ca93b6a1f3d142aca56de0282dd1fda2  Trace74CRTNaturalTuple.olean
bc83c2cc9a3ac1f94a41aca6e27ec921a4856ee358a92191130e89864df082b5  Trace74NegativeRankTuple.olean
3e119aaa5f400f8740d7412c7153f3fc0a14717e803a8b76092dfb5ca51f2196  Trace74RankCRTChart.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
