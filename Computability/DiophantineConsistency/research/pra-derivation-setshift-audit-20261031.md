# Set-shift witnesses in the derivation core

Foundation's actual `Derivation.blueprint` uses `setShiftGraph` in the
`allIntro` and `shiftRule` branches. In the positive core the former has an
existential output witness, while the latter places the output directly in a
graph. In the negative of the pi core, the negation of the corresponding
universal graph tests produces existential graph witnesses. These cases must
be bounded in arbitrary candidate-PRA models, not merely in the standard model.

`setShiftGraph` says that each member of the output is a shifted member of the
input, and that every member of the input has a shifted image belonging to the
output. The only unbounded existential inside that graph is the image in the
second conjunct. Its membership in the output bounds it by the output itself.
Thus a candidate-PRA `WB` proof for the graph can be assembled from the
existing `WB` proofs for `shiftGraph` and `bitDef`, with that local bound.
The conditional `PRAWitnessSetShiftGraph.wb_setShiftGraph` theorem has
and its `#print axioms` check compiled without warnings against an exploratory
overlay using rebuilt model-pairing, witness-calculus, transfer, and arithmetic
objects. The check reports `propext`, `Classical.choice`, and `Quot.sound`.
It still takes the shift-graph `WB` proof as an explicit hypothesis. The merged
`PRAWitnessFormulaFunctions.wb_shiftGraph` discharges it in
`PRAWitnessSetShiftCandidate.wb_setShiftGraph`; that specialization and its
axiom check pass on a partially inherited exploratory provider. The provider
compiled a source with an unused-instance linter warning, and its full parent
closure has not been authenticated.

For the separately quantified *whole output*, the merged
`PRAWitnessCodeGrowth.setShift_le` proves in every model of `IΣ₁` that

    setShift s ≤ 2^(2^(((s + 2)^2 + 13) · s² · 64 + 1)).

This expression is represented by one `BoundTerm.exp2` constructor with
multiplier 1: by definition `exp2 A B` already represents `2^(A · 2^B)`. The witness-transfer theorem uses the stronger
`IΣ₁` models only on the source side of the metatheoretic comparison; it does
not assert that arbitrary candidate-PRA models satisfy `IΣ₁`. The required
actual transfer, graph certificate and derivation-core assembly remain to be
checked. In particular this note does not establish the full refutation
witness bound, the HA equivalence, or source-current replay of the upstream
`PRAWitness` dependency graph.

The first exploratory dependency build stopped at `PRAHistoryTruncation`:
the historical `PRAModelIOpenPairing` object did not contain the newer
`standardModelISigmaZero` declaration. A replacement build is underway. The
failed build is not evidence for the newer upstream sources.

`PRAWitnessSetShiftOutput` now verifies the exact single-`exp2` bound and
uses `wb_exs_bt` to prove `WB` for the negated pi functional graph of actual
`setShiftGraph` in every candidate-PRA model. Its author replay passed with
standard Lean axioms on the same partially inherited, warning-qualified
provider. The exact all-introduction and shift-rule branches and full core
certificate still need assembly.

`PRAWitnessSetShiftExistential.wb_exs_setShift` lifts this output bound to
an existential over any arity and selected input position, when the body
implies the actual set-shift graph in `IΣ₁` models. Its guarded author replay
passes with the same inherited-parent and warning qualifications. An exact
derivation-rule body must still be matched to the theorem's hypotheses.

`PRAWitnessShiftRuleBranch.wb_neg_actualShiftBranch` now proves the negative
pi shift-rule disjunct in every candidate-PRA model. The theorem
`actualShiftBranch_eq` checks by definitional equality that the recognized
formula is exactly the eighth disjunct of Foundation's derivation core, for
any set theory with a `Δ₁` instance. The guarded author replay passed on the
same partially inherited provider. The other rule disjuncts and whole core
remain separate obligations.

`PRAWitnessWeakeningRuleBranch.wb_neg_actualWeakeningBranch` similarly
handles the literal seventh (weakening) pi disjunct, with syntactic identity
checked by definitional equality. It uses the `fstIdx` value bound and the
negative subset graph; the guarded author replay is provisional on inherited
parent objects.

`PRAWitnessNegExistential.wb_exs_neg` transfers the existing negation growth
bound for arbitrary selected arguments. `PRAWitnessIdentityRuleBranch` uses
it to establish the complete negative pi identity disjunct, with syntactic
identity to Foundation's first core disjunct checked by definitional equality.
Its guarded author replay has the same inherited-parent/warning caveats.

`PRAWitnessCutRuleBranch` establishes the literal negative pi cut disjunct,
with Foundation's ninth branch checked by definitional equality. Both
`fstIdx` outputs and the nested negation output are bounded. Its guarded
author replay retains the inherited-parent and linter-warning qualifications.

`PRAWitnessVerumRuleBranch` establishes the literal negative pi verum
introduction disjunct, with Foundation's second branch checked by definitional
equality. Its guarded author replay passed before the `PRAWitnessSetTerms`
unused-instance fix; its inherited-parent qualification remains.

The remaining negative pi branches were assembled into
`PRAWitnessNegativePiCore.wb_neg_corePi` on the exploratory provider. The
proof identifies the full Foundation pi-tail disjunction by definitional
equality and combines all ten branch bounds with the existing formula-set
conjunct. Its sole open theory-specific input is the negated-pi `WB` of the
axiom recognizer. A ZFC specialization using `goodCh_zfc` has been written,
but is not established until the strict 35-module source-frozen replay
completes. The independently replayed strict ZFC recognizer provider is now
available; its Foundation/ZFC Instances/package transitive ancestry is
inherited.

The complete 35-module strict negative-core suffix has now passed author and
independent replay with all source/object/log rows matching. It includes
`PRAWitnessZFCNegativePiCore.wb_neg_zfcCorePi`, which discharges the axiom
recognizer premise using `goodCh_zfc` and proves the actual ZFC derivation
core's negative pi witness bound in every candidate-PRA model. The final
axiom audit has only `propext`, `Classical.choice`, and `Quot.sound`. The
strict provider has a rebuilt 214-module local project closure and guarded
direct external anchors; external transitive ancestry is inherited. This is a
model-wise monotone `WB` result, not a claimed uniform PR code or the final HA
equivalence.
