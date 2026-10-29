# The three-disjunction induction-rule case

`ParsonsRule` defines a finitary proof type for an arbitrary first-order
ordered-ring language and closed base theory. Its constructors admit actual
Foundation LK derivations, base-theory axioms, modus ponens, universal
introduction and specialization, and the **Σ₁ induction inference rule**.
Its judgments are open formulas with free parameters. This defines the
intermediate calculus; it does not posit conservation, add IΣ₁ induction
axioms, or claim this calculus has already been shown equivalent to PRA.

`three_disjunctions` is an actual proof-object transformer. Given Σ₁ formulas
φ(x) and E, any term t, and exactly the three proof objects

```
base φ ⋎ E
step φ ⋎ E
¬φ(t) ⋎ E
```

it constructs a proof of E. It applies the induction rule to the guarded
formula `φ(x) ⋎ E`, specializes at t, and resolves the result with the third
premise. The input term and both formulas may have arbitrary free parameters.
The essential implication from `step φ ⋎ E` to the guarded step is itself a
concrete Foundation LK derivation: the universal case shifts the side formula
and all existing parameters, and the proof uses no unverified inference rule.
The guarded formula's Σ₁ classification and exact substitution are from
`ParsonsGuard`.

Both source files were snapshotted and compiled twice in fresh private outputs
under Lean 4.32 with `-M6000 -j1 -DElab.async=false`. Both objects and complete
logs match; no warnings were emitted. Eight axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The [16-file replay manifest](parsons-rule-replay/FILES.json)
has SHA-256 `fe277a671b47067cc0db9c68997b2610f0ae66d1edc01f2a134606b55f5ab5c2`.
The direct `ParsonsGuard` object was selected from its previously checked fresh
provider, SHA-256 `6ed2a4c0e10113e0c82c64ca7a4e05c0ff965a51f1ed3e3ad16400d3d7a728d1`;
Foundation and Mathlib compiled objects remain an inherited boundary, not a
fresh transitive source audit. Development scratch failures, including binder
rewriting and a mistakenly ungeneralized parameter, preceded the final builds;
their console logs were not retained.

This closes the isolated guarded inference, not the entire IΣ₁-to-rule
conservation proof. In particular, a bridge from finite cut-free theory
sequents to this calculus, handling every last rule and strict Π₂ normal forms,
and a proof that its Σ₁ rule is admissible in the chosen PRA presentation,
remain to be established.
