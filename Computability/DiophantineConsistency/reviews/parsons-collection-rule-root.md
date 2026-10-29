# Collection-rule induction predicate and base

`ParsonsCollectionRule.collector` is the formula
`k ↦ ∃B ∀i<k ∃y<B D(i,y)` with all free parameters retained.
`collector_sigma` proves it is Σ₁ in Foundation's hierarchy whenever D is Σ₁,
including the bounded quantifiers in D; it does not require a prenex theorem.
`base_logic` gives an LK derivation of the base case from `∀i ¬i<0`.
`zeroMin_paminus` proves that arithmetic fact from Foundation's actual
PA-minus theory using its model-theoretic completeness theorem and embeds the
result in the explicit rule calculus. Thus `paminus_base` constructs an actual
rule proof of the collector base without an extra arithmetic assumption.
This use of completeness and choice proves existence; no primitive-recursive
proof transformer is claimed.

`collect_if_step` is only a **conditional** assembly: given a rule proof of
`∀i ∃y D(i,y)` and an explicit rule proof of
`(∀i ∃y D(i,y)) → step(collector D)`, it constructs the full collection-rule
conclusion by the Σ₁ induction rule, with the proved base and complexity
certificate. The second input is exactly the unresolved finite-extension step;
it is not a proved collection rule or an assumption hidden as an axiom.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Seven
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The [16-file replay manifest](parsons-collection-rule-replay/FILES.json) has
SHA-256 `4630097193dd072b08a00c4dcea8993cb9192fa3977825e5490dc6182539f29f`.
Direct prerequisites were previously built `ParsonsCollection`,
`ParsonsPrenex`, `ParsonsRuleEmbedding`, `ParsonsCutFree`, `ParsonsRule`, and
`ParsonsGuard`; Foundation/Mathlib and completeness objects remain an inherited
boundary, not a fresh transitive source audit. Scratch attempts around binder
indices and the semantic PA-minus proof failed before being fixed; their
console logs were not retained.

The forward collection inference, including the finite-bound extension proof,
the guarded positive-context adapter, global cut-free recursion, and PRA
witnessing remain open.

## Independent root replay

A third build at `/tmp/parsons-collection-rule-build-b3nb5wyb` passed. Its
source, object and complete-log hashes match the first author build for both
modules. All seven direct prerequisite source snapshots match the current
checkout. The build still inherits the existing Foundation, Mathlib and
repository object caches; this is not a fresh transitive dependency audit.
The independent [driver, snapshots, logs and state](parsons-collection-rule-replay/root-build/)
are preserved. The finite-extension assumption remains open.
