# Counterexample case with a finite guarded context

`ParsonsCounterContext.counter_guarded` handles the induction counterexample
case for an **arbitrary finite marked context** whose side occurrences each
carry a `Guard` descriptor. Base and induction-block entries are allowed in
any position. It selects and freshly opens any universal side without adding
permutation or contraction steps, shifts the other marked entries, and recurses
on the strictly decreasing sum of side-formula complexities. Once the entire
projected side is Σ₁ it invokes the previously proved induction-rule case;
the resulting rule proof is then universally closed at each recursive step.

The theorem explicitly assumes `Below H`: every marked cut-free derivation of
height below `H` has already been translated to a rule proof. The original
existential conclusion must have height at most `H`. Neither that strong
hypothesis nor the `Good` side descriptors are proved here. In particular,
the induced `stepMark` side can be non-prenex Π₂ and need not have a `Guard`
descriptor, so restricting a global recursion to `Good` contexts would not
close the remaining cases. General Π₂ source normalization is still needed.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-counter-context-replay/FILES.json) has
SHA-256 `2f3a1d0ce34107d839086c43282129ead5125fe8554043e74d887c323a7bfc2e`.
The direct `ParsonsGuardContext` source hash
`b99064b9dcb6bfcaa28e7ee4386dcb5f7ff7c3990beaeb7c0854feca4e6a266b` and
`ParsonsFreshContext` source hash
`7c1f040a6c590948337157d71c1e9238ddca37258614a7416d44beaef9f83cd7`
match their frozen snapshots; their object hashes are respectively
`9e020252008aef0a2f8b056da37c5e7319b7de6c1c191811fb75c50a9c41343b` and
`c9aada04e471738fc448705119707978c9cc9eddc3a6b30f78a3a8b3da854b53`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

This is the conditional local counterexample case, not the global induction,
conservation theorem, candidate-PRA bridge, or PRA-provability result. The
separate HA theorem for the maintained 14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-counter-context-build-ku417f42`
passed with matching sources, objects and complete logs under the same
inherited-provider qualification.
