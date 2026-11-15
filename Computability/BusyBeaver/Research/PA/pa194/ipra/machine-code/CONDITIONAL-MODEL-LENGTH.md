# Conditional model-length physical/source composition

`PA194ConditionalModelLength.simulateModelLength` is a Lean theorem about any
candidate-PRA model whose arithmetic reduct satisfies IΣ₁. It proves, for
**every model element n** including nonstandard n, the conjunction

```
good(state n) ∧ stepper(elapsed n, start) = frame(state n).
```

The following are explicit hypotheses, not results discharged by this theorem:

* The displayed conjunction, as a predicate of n, is Σ₁-definable in the model.
* The conjunction holds at zero (this includes whatever startup/frame and
  initial-clock alignment are needed).
* `state(n+1) = next(state n)` and
  `elapsed(n+1) = elapsed(n) + cost(state n)` in the model.
* `good` is preserved by `next`.
* For **every** good modeled state s, the literal packed stepper run for
  `cost(s)` steps from `frame(s)` equals `frame(next(s))`.

The proof applies internal model IΣ₁ induction to the stated definable
invariant and the existing `PA194StepperCompose.modelStepperCompose` to join
adjacent literal segments. The 60-module coherent machine build is used for
the latter theorem. The generic functions and predicates are not yet bound to
the concrete scheduler; in particular, this theorem does not construct a
cumulative clock code, prove definability, the all-site segment hypothesis or
its halt correspondence. It is a conditional Lean theorem about models, not
an object-theory iPRA derivation and not either PA consistency implication.
The Lean axiom audit lists `propext`, `Classical.choice` and `Quot.sound`,
without `sorryAx`.

## Staged replay

`check-conditional-model-length.sh` pins and recompiles this source in a fresh
output against the separately built coherent machine baseline and two general
project/foundation roots. It verifies the coherent manifest and direct stepper
objects but does not itself rebuild or authenticate their transitive closure.
The earlier startup/header baseline, general logic and Lake/Mathlib objects are
staged prerequisites. Paths below are session-local.

From the repository root:

```sh
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
bash "$base/check-conditional-model-length.sh" \
  "$PWD" "$base/PA194ConditionalModelLength.lean" \
  /dev/shm/pa194-unified-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker rejects inherited Git-internal overrides and does not set them.
