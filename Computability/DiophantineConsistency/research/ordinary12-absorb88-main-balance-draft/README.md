# Oriented main Pell balance for the 88 negative branch

`graph_main_balance` proves the following for the indicated models of IΣ₁.
Given an actual positive 88-graph zero, `beta>0`, and the additional negative
transport hypothesis `ιBp < ιBn`, there exists a model element `g` such that

```
g² = 1 + delta(a)*c²,
Dstar = ιW * ιg
```

in the model difference ring, where `Dstar` is the evaluated
`(Absorb89Main.mainParts ...).1` and the other registers are defined in the
Lean statement. The same main residual belongs to the 88 graph. The proof
uses the prior evaluated-root positivity, the actual main residual, and an
extracted main Pell root to choose the positive square-root sign.
`main_rhs` separately identifies the evaluated right-hand side of the main
factor. The source's `Draft` comment predates the check recorded below.

The theorem assumes the negative branch; it does not prove the signed rank
window or rank congruence, construct an 89 witness, or establish an iPRA
endpoint. The existing 89 window depends on positive transport and is not
available automatically here.

A possible next step, not proved by this file, is to derive the signed
divisibility `q^5 ∣ H*(k−R−1)` from the balance and `W=q^5*s`, then
use a signed-to-natural magnitude bridge to apply the existing factor
cancellation theorem. Even a resulting `q^4 ∣ (k−R−1)` would not by
itself supply the missing rank window.

## Observed check

On 2026-11-04, Lean 4.32.0 exited 0 and reported both declarations depend on
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or warnings.
From the repository root, with the previously checked local objects in `/tmp`:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:/tmp/absorb89-chain-gpc9zymd/lib:$TASK_LEAN_PATH \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-main-balance-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-main-balance-draft/Absorb88MainBalance.lean \
  -o /tmp/Absorb88MainBalance.olean
```

Source SHA-256:
`8b96901410c94bce76043a0e6e183d14c36b0f617a1cb897fe2ff6fce6609806`;
output SHA-256:
`ec231619db9f3830626678b9d553bbaa5b6727f73443fd2afa8e2ff514026267`.
The direct `Absorb88MainEvaluation.olean` input SHA-256 was
`55a73dfa0857e26f914c103b63d447cc7bbbbf42dd5afd46276a850429897cb6`.
Temporary prebuilt providers were inherited; their complete project,
package, dynamic-library and search-path ancestry was not audited.
