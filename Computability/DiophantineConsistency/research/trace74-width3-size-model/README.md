# Width-three lower power estimate in arithmetic models

`Trace74Width3SizeModel.lower_power_bound` proves, in any model of `IΣ₁`,

```text
16384 h³ K⁶ < power Y (d+3)
```

under the explicit hypotheses `q ≥ 2³⁰`, `q³ ≤ Y`, `h < q`,
`r ≤ d+15`, and `K = power 2 r`. Here `power` is represented model
exponentiation, so `d` and `r` need not be standard numerals. For the
planned graph application let `d=n−12` with `n≥12`; then `d+3=n−9`
and `r≤n+3` supplies `r≤d+15`.

The proof takes `P=power 2 d`, obtains `P⁶ ≤ power Y d` from `Y≥64`,
and `K≤32768P`. The bound `q²≥2³⁵`, the cubic hypothesis on `Y`, and
`h<q` yield `Y>2³⁵h`; cubing this strict inequality exceeds the
coefficient `2¹⁰⁴=16384·32768⁶`. Fixed exponent identities and
positive-factor comparisons complete the proof without products of
variable exponents.

The theorem assumes these numerical and index bounds and does not itself
bind them to a graph zero, prove a reverse guard, or establish an iPRA
endpoint. In particular, `r≤n+3` is a conditional window, not a property
proved for every graph zero.

The author invoked Lean 4.32.0 with a captured provider and observed
session 11428 exit 0; the sole axiom report was `[propext,
Classical.choice, Quot.sound]`. The invocation was:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-width3-size-model \
  Computability/DiophantineConsistency/research/trace74-width3-size-model/Trace74Width3SizeModel.lean \
  -o /tmp/Trace74Width3SizeModel.olean
```

Source SHA-256 is
`57d0ff03273a6e71f907d91e54785d9d8695619c890e8d8398a74cadd66e8096`;
the output object SHA-256 is
`c5c19b202e4f444d9af79a3d22a50e1a195900285c96a9ecb0a810d71e9b3049`.
The direct imported `Trace74NearDiagonalSizeModel.olean` SHA-256 is
`dd4398cd1513c2e05fdca415c8fa76a75c4d40862fe2d7a5db3047df054f1513`.
One earlier author check failed on an elaboration mismatch in a
multiplication order argument. The temporary provider paths, their
transitive dependencies, and search-path selection have not been
independently authenticated; this is not a clean current-source rebuild or
an independent replay.
