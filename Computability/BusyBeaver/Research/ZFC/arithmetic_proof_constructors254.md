# Accepted constructors for the original arithmetic validator

[`ArithmeticProofConstructors254`](../../Lean/BusyBeaver/ZFC/ArithmeticProofConstructors254.lean)
proves exact constructor equations in every IΣ1 model. The generic
`value_node` theorem normalizes the quotient and remainder of
`12 * payload + tag` for `tag < 12`, then applies the unchanged validator's
complete-history recurrence.

Its corollaries construct accepted proofs for truth, MP, GEN, all eight
original logical rows and the bundle. MP retains its original predecessor
and implication gate; GEN uses the entire child-code tail; the bundle
requires both original freshness inequalities. Every operand, payload and
child code may be internal. Proof code 0 remains invalid and proof code 1
proves truth. The node constructor has a fixed Σ0 graph and an exact ordinary
Nat identity with `Code254Proof.node`.

The [fresh source/audit check](results/arithmetic-proof-constructors254-verification.json)
passes seventeen axiom reports and eighteen callers, using only standard
Lean axioms and emitting no warnings. It reuses eighteen matched project
modules from the actual `ArithmeticHistoryRecurrence254` import closure.
The [independent review](results/arithmetic-proof-constructors254-review.json)
checks the source, audit, exact artifacts and role in the planned soundness
invariant.

The portable checker takes a successful **RefutationWord** record as an
inventory of available providers. It selects only the eighteen actual
prerequisites; no compiler or refutation module is imported by this source.
Its maintained-default preparation passes and is recorded separately from
the successful Lean proof check.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_proof_constructors254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --refutation-evidence /outside/successful-refutation-word/verification.json \
  --output /outside/new-empty-constructor-check
```

These equations provide explicit proof witnesses for the planned
[bounded stack invariant](arithmetic_enumerator_soundness_plan254.md).
They do not yet prove scheduler soundness, translate ZFC proof codes or
establish the PA equivalence for the binary machine.
