# Exact even-half-index auxiliary Pell residue

`Trace74ExactAuxPellResidue.even_quotient_mod_norm` proves in every `IΣ₁`
model the **positive** residue branch

```text
oddQuotient (2t) (I−2) mod f = ycoord (4t+1) a mod f,
```

under the explicit hypotheses `I≥2`, `f>0`, and
`I²+delta(a)=delta(a) f²`. It strengthens the existing signed-disjunction
result at even half-indices. The represented Pell/quotient functions and
induction are internal to the model; the proof separately tracks the even
and odd stages in a two-step `Σ₁` induction.

This is an arithmetic lemma only. It does not supply its norm hypothesis,
construct a graph witness, prove a reverse guard or establish an iPRA
endpoint. In the proposed coupled-Pell construction it is the exact sign
needed before further addition, CRT and positivity arguments.

Lean 4.32.0 was run with:

```text
LEAN_PATH=/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-exact-aux-pell-residue \
  Computability/DiophantineConsistency/research/trace74-exact-aux-pell-residue/Trace74ExactAuxPellResidue.lean \
  -o /tmp/Trace74ExactAuxPellResidue.olean
```

Actual session 59399 exited 0 without warnings; the sole axiom report
lists only `propext`, `Classical.choice`, `Quot.sound`. Earlier runs
failed on elaboration and are not accepted. Source SHA-256:
`f139de91a80e75e1bd8f6c8317b36db34d03e06cfcc3fa59d30057f92f4ca123`.
Object SHA-256:
`554cc19fb4b5e426ad7ca0ddf104032fdd8880b29733f139ab8a8e9efcf79880`.
Direct imported `ArithmeticPellHalfIndex.olean` SHA-256:
`6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7`.
This is a captured-provider author check, not an independent replay or a
coherent current-source build. Full transitive, package and dynamic
ancestry and search-path selection remain outside this check.
