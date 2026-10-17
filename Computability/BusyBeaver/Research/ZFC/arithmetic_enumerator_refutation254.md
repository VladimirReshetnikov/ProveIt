# PA proves the validator-to-scheduler implication

[`ArithmeticEnumeratorRefutation254`](../../Lean/BusyBeaver/ZFC/ArithmeticEnumeratorRefutation254.lean)
proves a fixed arithmetic sentence in IΣ1, and hence in PA: if the unchanged
validator accepts a proof of falsity, the represented scheduler halts. The
scheduler starts with pointer and next-candidate registers zero; its four
working registers may be arbitrary.

The proof composes the [represented refutation word](arithmetic_refutation_word254.md)
with [internal candidate fairness](arithmetic_enumerator_run254.md). Every
accepted falsity proof supplies a positive word halting from every working
state. The scheduler reaches its raw candidate, which is the shifted word
minus one, unless it has already halted. All proof codes, candidate indices
and times in this argument range over the arbitrary IΣ1 model.

The fixed `forwardSentence` explicitly uses the original `valueDef`, scheduler
`liveDef` and `runDef` graphs:

```text
forall code, work,
  valueDef(2, code) ->
    exists initial,
      liveDef(initial, 0, 0, work)
      and exists time, runDef(0, time, initial).
```

Here validator output 2 means conclusion 1 (falsity) plus its acceptance
marker, while scheduler output 0 denotes halt. Arithmetic completeness turns
the theorem in every IΣ1 model into `isigma1_proves_forward`; weakening gives
`peano_proves_forward`. The sentence and graph definitions are fixed before
choosing the model.

The [fresh source/audit check](results/arithmetic-enumerator-refutation254-verification.json)
passes five axiom reports and nine callers, including arbitrary working
registers, the explicit graphs, IΣ1 and PA derivability, and the contrapositive
from scheduler nonhalting. It uses only standard Lean axioms, emits no
warnings and reuses 41 matched project modules. The
[independent review](results/arithmetic-enumerator-refutation254-review.json)
checks the complete source, audit and exact dependencies. Maintained-default
portable preparation is recorded separately and invokes no Lean process.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_enumerator_refutation254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --run-evidence /outside/successful-enumerator-run/verification.json \
  --refutation-evidence /outside/successful-refutation-word/verification.json \
  --output /outside/new-empty-enumerator-refutation-check
```

The represented validator is the C254 proof checker. This theorem supplies
one direction of its comparison with the represented scheduler. The reverse
direction requires a soundness invariant from a certified initial state;
arbitrary dirty states can already contain falsity in cache. Binary-machine
transport and internal C254/ZFC proof transformations remain open. The
requested PA equivalence for the 252-state blank machine is therefore still
unfinished.
