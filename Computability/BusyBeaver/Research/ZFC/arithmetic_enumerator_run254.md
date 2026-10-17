# Internal fair enumeration of actual command candidates

[`ArithmeticEnumeratorRun254`](../../Lean/BusyBeaver/ZFC/ArithmeticEnumeratorRun254.lean)
iterates the exact [scheduler step](arithmetic_enumerator_step254.md) with one fixed Σ₁ primitive-recursion blueprint. Its run graph is total Δ₁ at every internal time in every IΣ₁ model. Halt code zero is absorbing. A live state with pointer zero remains a candidate boundary that will resume at the next tick.

A word evaluator and a scheduler are paired by `embedValue np config`: evaluator halt maps to scheduler halt, while a positive evaluator maps to the same remaining word and working state with fixed next candidate `np`. Their steps commute only while the word is active. The Σ₁ time invariant records either current alignment, or a bounded earlier time at which the word had stopped and the two states were aligned. The latter witness is frozen. This avoids assuming that a scheduler remains aligned after its boundary has started another candidate.

The actual word drain theorem supplies a stopped time by the shifted word's code bound. Word absorption identifies this stopped result with the terminal word evaluator, giving `drain_terminal` and `drain`. `drain_boundary c w` counts the first fetched command once, then drains its remaining tail. It obtains a witness `t ≤ c+1` with the exact halt or completed working-state result of `evalValue (c+1) w`. The shifted word is `c+1`; raw candidate zero genuinely executes MP0.

`reach` uses Σ₁ induction on the internal candidate index. Its time and working-state witnesses are existential, so it needs no universal changing-state induction hypothesis or register-size bound. From a scheduler boundary at next candidate zero and any initial working-state code, every candidate boundary is reached unless the scheduler has already halted.

`halts_of_word` concludes that any positive internal word halting from every working-state code is eventually executed. Its target raw candidate is `word−1`, and the positive-word hypothesis justifies `(word−1)+1=word`. It does not assume that any particular compiled refutation word exists, and it proves no converse soundness statement. The subsequent [composition](arithmetic_enumerator_refutation254.md) proves the validator-to-scheduler implication in PA. Transport to the binary machine and the PA consistency equivalence remain open.

The [successful fresh check](results/arithmetic-enumerator-run254-verification.json)
compiled only this module and its 16-probe/13-caller audit, using an exact 26-project import closure from checked SchedulerStep14/12 and Execution15/20 records. It uses only standard Lean axioms and emits no warnings. The
[independent review](results/arithmetic-enumerator-run254-review.json)
checks the full proof and exact artifacts. Four actual first external provider identities, every direct external import, the compiler, dependency pins, sources and objects were checked before and after. The two records include byte-distinct Cantor objects from the same source; the selected SchedulerStep object is the actual first provider, while the other is recorded as unused historical dependency metadata and separately hashed. No object identity is inferred from equal source text.

The portable runner `check_arithmetic_enumerator_run254.py` accepts explicit `--repo`, `--dependency-root`, `--step-evidence`, and `--execution-evidence`, with optional `--step-cache` and `--execution-cache` for separate relocated overlays. Separate overlays matter for the two Cantor object identities. Maintained source and audit defaults have frozen hashes. Old dictionary and maintained list formats for external provider metadata are accepted. `--prepare-only` performs preflight/postchecks and records `PREPARED_NOT_BUILT` with no Lean commands. The prepare-only schema-normalization control changes metadata formatting only and does not constitute another proof replay.

The subsequent [ordinary-Nat adapter](arithmetic_enumerator_run_nat254.md)
identifies this run with actual `Enum254.run` at every ordinary time and
state, including an exact comparison with its native blank-halting predicate.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_enumerator_run254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --step-evidence /outside/successful-enumerator-step/verification.json \
  --execution-evidence /outside/successful-command-execution/verification.json \
  --output /outside/new-empty-enumerator-run-check
```
