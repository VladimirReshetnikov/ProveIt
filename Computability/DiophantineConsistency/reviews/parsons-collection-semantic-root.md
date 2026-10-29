# Finite extension and a parameter-free collection rule

`ParsonsCollectionSemantic.semantic_step` proves directly in Lean that in
every PA-minus model and under every free-variable assignment, totality of
D implies the collector's induction step. The proof combines an existing
bound B and a witness y by choosing `B+y+1`. `step_closed` applies Foundation's
arithmetic completeness theorem to obtain an actual PA-minus proof of the
universal closure of this implication, for every D; no Σ₁ assumption is needed
for this finite-extension theorem.

`step_proof_closed` embeds that theorem into the rule calculus when the exact
implication `total D → step(collector D)` has no free variables.
`collect_closed` combines it with the previously proved PA-minus base and the
Σ₁ induction rule. It is a complete proof transformer for this explicitly
parameter-free case: a rule proof of totality yields a rule proof of bounded
collection, without assuming a finite-extension proof. The exact syntactic
closedness condition is a hypothesis; the file does not prove it from a more
general condition on D. The completeness-based construction is noncomputable
and establishes existence rather than a primitive-recursive proof transformer.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Four
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-collection-semantic-replay/FILES.json) has
SHA-256 `0beafe5dcfe9bcde8373b79e344f6c9e79d2c6128e93f9649e030429b6a88428`.
Direct prerequisites were previously built `ParsonsCollectionRule` and its
providers. Foundation/Mathlib and completeness objects remain an inherited
boundary, not a fresh transitive source audit. Scratch attempts on evaluation
and completeness simplification failed before being fixed; their console logs
were not retained.

The arbitrary-parameter collection rule still needs an actual specialization
of the closed theorem back to its open finite-extension formula. The positive
guarded-context adapter, complete strict Π₂ normalization, global cut-free
recursion, and PRA witnessing remain open.

## Independent root replay

A third build at `/tmp/parsons-collection-semantic-build-z2wrjxx9` passed;
its sources, objects and complete logs match the author build. The direct
`ParsonsCollectionRule` provider has the same object hash as the independently
replayed and committed source. The [independent build artifacts](parsons-collection-semantic-replay/root-build/)
are preserved; inherited package and Foundation caches remain a qualification.
