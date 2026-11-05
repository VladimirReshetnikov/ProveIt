# Modular Pell binary steps

`Trace74PellModularBinary.even_step` and `odd_step` prove, in every IΣ₁
model, the correctness of binary index transitions for the represented
Pell recurrence modulo any positive internal modulus. Given residues
`X,Y` congruent to the actual coordinates at internal time `t`, write

```
A = X*X + delta(b)*Y*Y
B = 2*X*Y.
```

The pair `A,B` gives the coordinates at `2t` modulo the modulus, and
`((b+2)*A+delta(b)*B, A+(b+2)*B)` gives those at `2t+1`. All quantities
can be reduced modulo the modulus between steps. This supports a
logarithmic-length binary certificate without constructing the enormous
Pell ordinate, including when the input index is internal.

These are transition lemmas, not yet a complete list-of-bits evaluator,
nor a checked result for the 32-bit candidate index. They do not prove
the base reduction, the finite gcd/Bézout certificate, the external
payload binding, graph zero, or an iPRA endpoint. See the
[concrete certificate assessment](../trace74-concrete-crt-certificate-assessment/README.md).

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and the previously built dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-pell-modular-binary Computability/DiophantineConsistency/research/trace74-pell-modular-binary/Trace74PellModularBinary.lean -o /tmp/Trace74PellModularBinary.olean
```

Both results report `[propext, Classical.choice, Quot.sound]`. SHA-256:

```
953e4af82f88166af7d63557d43da0527b067fc932b3bb95610cc30ad7896eb6  Trace74PellModularBinary.lean
f0a8f423ed4b78497b71eb25903fc2581b7091a298cab6e53d266b68902d3a5a  Trace74PellModularBinary.olean
72a39b10f02e78f21c791df8c98337a6f5e8a09f46f0381265b79dee8205d9ea  ArithmeticPellPeriodicity.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
