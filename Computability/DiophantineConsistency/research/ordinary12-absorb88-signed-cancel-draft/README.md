# Signed factor-three cancellation in a model difference ring

In the indicated IΣ₁ models, `natural_of_embedded_dvd` proves that
divisibility of two embedded natural-model elements in the model difference
ring implies their divisibility in the model. Its proof handles both signs
of the ring quotient; a negative quotient can only produce zero when the
embedded dividend is nonnegative.

`cancel_signed` then proves, for `q>0`, `q³ ∣ Y`, and any difference-ring
element `x`,

```
q⁵ ∣ (3+4Y(X+1))*x  →  q⁴ ∣ x.
```

Powers, coefficients and divisibility in this display are interpreted in the
difference ring after embedding the natural-model elements. The proof splits
`x` into an embedded natural or its negative, applies the checked natural
`cancel_factor_three` theorem, and restores the sign. This module does not
itself instantiate an 88 graph zero, prove a rank window or produce an iPRA
endpoint. Its `Draft` source comment predates the observed check.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0; both theorems reported axioms
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or warnings.
From the repository root:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:$TASK_LEAN_PATH /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-cancel-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-cancel-draft/Absorb88SignedCancel.lean \
  -o /tmp/Absorb88SignedCancel.olean
```

Source SHA-256:
`1117e85e01cdd1c5bc7946dd41c4a27536bcf0a0175f7299d30cdbd136cc290f`;
output SHA-256:
`943a6d105f7885fe99e53679924800494561c80957cff2c9ad34026ba1a7bf47`.
Direct imported object hashes were `a8c24451f02c95a5e4a4c8a2a3f91b806717a44cb11cac09a32d5d854f84c5bb`
for `ArithmeticAdaptiveFactorThree2011` and
`d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74`
for `ModelDifferenceRing`. The full transitive source/object, package,
dynamic-library and search-path ancestry was inherited, not independently
audited.
