# Conditional iPRA endpoints for package 65

This Lean packet proves native, standard and equality-only iPRA equivalences
between the positive-shifted P65 graph's nonexistence of zeros and the mapped
Foundation ZFC consistency formula, **conditional on** `ReverseDirection`:
in every IΣ₁ model, a positive zero of this exact fixed-port graph implies
an internal halt of machine 215. `ReverseDirection` is an explicit theorem
hypothesis; it is not proved by this packet. The other model direction is
`P65CanonicalHaltConverse.halt_positive_zero` and requires no extra model
hypotheses beyond the displayed halt.

The underlying expression is exactly
`(P65Graph.graph (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output`.
The syntactic formulas use `positiveShift expression` so natural zeros of the
shift correspond to strictly positive coordinates of the original graph. This
statement concerns the Lean graph and the repository's mapped consistency
sentence; it is not an assertion about the displayed 65-operation PDF. The
P65 `P65Facts.halts` source is a candidate for discharging the hypothesis,
but has not been built or connected in this captured-provider check.

Lean 4.32.0 compiled the source in actual session 79962, exit 0 without
warnings. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`
for the polynomial bridge and all three conditional endpoints. This is a
captured-provider check: the path and shim ancestry caveats of
`research/p65-canonical-data-binding/README.md` apply unchanged.

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/p65-ipra-halt-reverse-adapter \
  research/p65-ipra-halt-reverse-adapter/P65IPRAHaltReverseAdapter.lean \
  -o /tmp/P65IPRAHaltReverseAdapter.olean
```

Source SHA-256 `42e1b330c1e8a879c003e0adebd4e20a854e0e9d8e82d0ac8d65feb0a688f962`;
object SHA-256 `1db9b2f6064155618a7f14c12c2affa74c5faaf66ce94493b8c9bc8d26fd9636`.
