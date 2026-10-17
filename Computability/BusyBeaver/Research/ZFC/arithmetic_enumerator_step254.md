# The actual arithmetic scheduler step

[`ArithmeticEnumeratorStep254`](../../Lean/BusyBeaver/ZFC/ArithmeticEnumeratorStep254.lean)
supplies one fixed Σ₁ graph, with a Δ₁ total-function graph, for one complete iteration of the original six-register `Enum254` controller. A live configuration is `1 + P(pl,P(np,W))`, where `W = P(tw,P(ws,P(d,h)))`. Configuration zero is absorbing halt. Every positive configuration decodes exactly.

The two fetch branches remain distinct. If `pl = 0`, execute the actual raw candidate `np` and install next candidate `np+1`. Otherwise execute raw command `pl−1` and preserve `np`. The existing checked command effect and actual tail extractor determine the remaining working registers and list pointer. Raw candidate zero is a genuine MP0 instruction; shifted word zero means no commands. A live boundary with `pl = 0` is not an absorbing completed word evaluator.

The graph and its correctness hold for every internal input in every IOpen model, without proof validity or standardness assumptions. `step_active_decreases` proves a shrinking pointer or a halt only when the old pointer is nonzero. It makes no decrease claim at candidate boundaries.

The all-Nat adapter `step_encode_nat` agrees with actual `Enum254.enumStep` on every ordinary scheduler state, including dirty values of all six fields. It uses the existing total command unpack/pack law, checked command-effect adapter, actual raw-rest formula, and `EnumStackBarrier254.execAt_unpack`. A small explicit uniqueness proof identifies Foundation's subtraction on Nat with ordinary truncated subtraction; no unproved instance coercion is assumed.

The [fresh check](results/arithmetic-enumerator-step254-verification.json)
compiles this module and a 14-probe/12-caller audit using exactly 21 source/object prerequisites selected from successful Rule evidence. The audit includes the actual zero-start candidate0 step, generic dirty six-field states, arbitrary raw commands, the two fetch branches, and active-only decrease. It uses only standard Lean axioms and emits no warnings. The
[independent review](results/arithmetic-enumerator-step254-review.json)
checks the full source, audit and exact artifacts. No dependency is fetched
or rebuilt. The subsequent [scheduler iteration](arithmetic_enumerator_run254.md)
now proves internal candidate reach. Transport to the binary table and the
PA consistency equivalence remain separate obligations.

The portable runner is `check_arithmetic_enumerator_step254.py`. Its maintained source/audit defaults have frozen hashes; `--rule-evidence` identifies successful Rule11/8 evidence, and optional `--rule-cache` supplies a relocated overlay of that evidence's 37 baseline objects. It selects only the exact 21 imported objects, checks all current source/object/provider identities and dependency/compiler pins, and repeats these checks afterward. `--prepare-only` never invokes Lean. External providers are reused with identified hashes, not independently rebuilt or attested as a complete dependency tree.

Example replay after publication:

```sh
python Computability/BusyBeaver/Research/ZFC/check_arithmetic_enumerator_step254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/Proofs-with-cached-Foundation \
  --rule-evidence /path/to/successful-rule-verification.json \
  --output /fresh/external/scratch
```
