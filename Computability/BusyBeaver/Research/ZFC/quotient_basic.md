# Empty Set, Pairing, Union and singleton closure in the quotient

`QuotientBasic.lean` derives Empty Set, Pairing and Union in the actual
CP/GIC bisimulation quotient. Its hypotheses are
`ProfileModel.ModelsCPGIC mem` and an explicit raw witness. It also derives
the upstream `INF_lib` property in that quotient, with exact singleton
formation expressed using quotient equality.

The resources are the existing formula-indexed collection instances.
Empty Set uses the false matrix; Pairing uses `pairs_of_model`; Union
uses the literal `CompositionModel.union_instance`. The quotient proofs
cover arbitrary elements by quotient induction, and Union lifts both
directions of its existential quantifier through representatives.
`quotient_pair_form` and `quotient_union_form` satisfy the repository's
actual `Pair_form` and `Union_form` under every valuation. A separate
`emptyForm` and its checked semantic equivalence express Empty Set.
These arguments follow upstream `S_ax.v:S_eset/S_pair/S_union` at
`297ab8df7e5de329605c3875b4934643b371a5e3`, through the attributed
profile and quotient modules.

`SingletonClosed mem` states

```text
∀ root, ∃ v, root ∈ v ∧
  ∀ x ∈ v, ∃ s ∈ v, ∀ z, z ∈ s ↔ z = x.
```

`singletonClosedForm` is the corresponding first-order sentence with
literal de Bruijn indices; `sat_singletonClosedForm` checks its exact
meaning. The proof uses `singleton_closed_of_containers`, following
upstream `S_ax.v:S_inf`. Quotient induction converts raw bisimulation
equivalence in its singleton condition to actual quotient equality.
`quotient_empty_singleton_container` specializes this property to an
actual empty quotient object. This is the interface needed for the next
Infinity argument.

Singleton closure does not assert closure under the von Neumann successor
`x ∪ {x}`. No theorem here has target `Inf_form` or `ZFAxioms.inf`.
The ordinary Infinity bridge, Regularity, Choice, the opposite
ZFC-to-source interpretation and the machine endpoint remain separate.
The generic module adds no IR, raw Extensionality or profile-congruence
hypothesis. Encoded-bundle models can enter through `Code254GIC` with
that adapter's explicit IR and valuation hypotheses. No table or state
count changes.

The 165-line module compiles with the explicit pinned Lean 4.32.0 compiler
in 0.37 seconds. All 15 theorem axiom audits and three callers pass.
The callers check Pairing/Union field compatibility with `ZFAxioms`, a
closed `sealF singletonClosedForm`, and composition from EncBundle models
to all four quotient sentences. The first caller supplies the other
`ZFAxioms` fields separately; it does not construct a complete ZF model.
Dependencies are limited to `propext`, `Classical.choice` and
`Quot.sound`; there are no admissions or custom axioms. An independent
machine-proof-agent read found the resources, formula indices,
representative coverage and stated scope clean. Commands and results
are recorded in `results/quotient-basic-verification.json`.
