# Further logical-proof simplification, latest review

Latest reviewed main:53269bcab1efc0f82d3022645bd7cf0c22d84959. The commit-review worker verified that KSeedModel222 is byte-identical to05d063acef885d47be5a2ce6645b046f98f7ea02; its blob remains3f7d09a5c50e6b237305727ee8d66bcfc2fef467. New DR215/formalism notes are research input, not maintained Lean/Rocq changes or new compiled endpoints. All proposals below are uncompiled: no Lean/Rocq binary was found.

## 1. Remove a third unnecessary formula induction

The previous semantic-roundtrip proposal removes enc_dec_enc and eqFree_dec_enc. It leaves enc_pos only to establish the padded matrix code exceeds1. That is unnecessary:

    enc(¬¬ψ) = 4*P(enc(¬ψ),1) >=4 >1,

by the RIGHT projection bound alone. No positivity or structural property of ψ is needed.

KSeedModel222.proposed.lean now removes all three inductions. It changes the bound to:

    have h := le_P_right (enc (negNF ψ)) F
    change 1 < 4 * P (enc (negNF ψ)) F
    unfold F at h ⊢
    omega

The combined patch is270→235lines, net35lines removed,10more than the prior proposal. It preserves seed_eqFree's exact statement and the numerical calculus. Public compatibility lemmas can be retained temporarily if external callers exist; the lower-chain proof itself no longer uses them. Semantic roundtrip remains necessary and is reused, not assumed. See REMOVE_THREE_INDUCTIONS.patch.

## 2. Replace the model's oversized axiom premise by exactly the seed schema used

NARROW_SEED_INTERFACE.md specifies SeedTheory consisting only of equality-free double-negation-padded bundles at roles0,1. Show every member's interpreted code derivable by a direct C222.bundle instance. Existing seed_eqFree only uses this family, so its model premise can be weakened from all DerivableNF formulas to SeedTheory. Invoke the already generic KEind222.c222_complete on this smaller theory.

This is a concrete dependency/interface simplification; no new model-consistency argument is required. It does not promise fewer lines, but exposes precisely what the lower proof needs and separates model axioms from numerical derivability. Equality interpretation, nonempty valuation, seed quotient and ZF interpretation remain. Restricting the lower theory does NOT justify restricting the raw upper soundness theorem or machine generator.

## 3. A common raw-calculus transport kernel for the new row variants

AxiomTransport.lean gives a small generic closure and proof by induction. Fixed data: a carrier A, truth element, implication operation, binder-index type, and theorem-only generalization operation. Variable data: an axiom predicate Ax:A→Prop. The closure has just axiom,truth,MP,GEN constructors.

The transport theorem needs exactly

    ∀a, Ax a → Closure Bx a.

Its conclusion transports every Closure Ax proof to Closure Bx. Mutual admissibility gives equality of theorem predicates, not merely equiconsistency. No injectivity, formula decoding, freshness, or substitution operation is involved. Numerical aliases are therefore harmless. To use it with current C222, prove once that its literal constructors are this closure for a tagged union of its axiom schemas, including every gate and dominance condition.

For DR215's changed sixth-row sampler, the two axiom image predicates are literally the same set:rho6(a,c) versusrho6(a,b), with both variables unrestricted. Each direction is a one-line axiom constructor after renaming witness. This does not say a fixed AX tuple has identical outputs; the source compiler still needs its repaired sampler block.

For the new antecedent-exchange family, each direction's axiom admissibility comes from the unchanged dominated-rho8-derived K/S basis and the exchange schema. MP/GEN proof transport is then generic. Crucially, exchange must be provable in BOTH target calculi from their unchanged common basis. Retaining a row only in the source does not suffice. Bundle gates/private labels are left literal. This kernel replaces repeated derivation-translation arguments with small axiom certificates; it does not replace numerical/ZFC calibration by an assumption.

Direct semantics or proof-assistant witnesses should establish those axiom certificates. An external Python truth-table PASS is not a substitute. AxiomTransport.lean's proof is an uncompiled source proposal, not a new certified kernel.

## 4. A finite propositional bridge shared by raw codes and named formulas

PropositionalProjection.lean proves the generic schema ¬(a→b)→a over an arbitrary carrier and Kalmar.Classical interface, using the existing kernel theorem tautology_complete and four Boolean cases. No formula-code freeness is required.

It collapses KEqCodes222.vrel_of_bundle's locally rederived projection to application of this one theorem:

    C222.mp (C222.bundle a b c hca hcb)
      (not_imp_left c222_classical (vrel a b c) (nks a b c)).

Only definitional unfolding of bundle222/wn is needed. The same schema handles named bundle projections. It can live with generic propositional lemmas rather than another machine-specific lemma. A new schema file for one call need not reduce total lines; sharing it across numeral and named syntax is the benefit. Existing Kalmar already permits noninjective implication, so do not introduce a stronger free-algebra interface.

## 5. A genuinely redundant hypothesis, and limits

KSeedModel222.matrix_iff currently carries hirr because its enclosing section says include hirr. Its entire proof is sat_dec_agree mem c E _ h, which does not require irreflexivity. Add omit hirr in immediately before matrix_iff and drop that argument at its callers. This is a valid strengthening of that helper only. sat_req and seed_of_bundle use sat_wn and still require irreflexivity; removing it there would be wrong. Do not extrapolate a helper's smaller premise to the endpoint.

No substantially shorter direct Seed→Con(ZF) route was established. Existing zf_consistent_of_formSeed uses the tagged-domain quotient interface to construct enough ZF structure, and the upper direction uses constructible-model seed validity. Merely postulating a generic model-extension theorem would hide, not remove, those obligations. The new narrow SeedTheory makes the true boundary explicit without changing it.

## 6. New-commit assessment

The DR215 formalism note establishes all-natural theorem equality for swapping curried antecedents in selected rows, with no GEN inside the deduction proof. This is sound as stated; replacing dual rho6 is explicitly NOT justified because its proposed derivation would borrow ex-falso from the very row being removed. DR215's literal rho6 sampler C→B preserves the axiom family but requires the repaired sixth-row compiler AX(a;a,v), producing A=a,B=v,C=a and disabling the irrelevant bundle gate. Existing startup/protected-tail and source/runtime obligations remain.

These changes offer cleaner generic proof interfaces, not evidence that DR215 has a shorter exact-table proof than K215. No214-state candidate, new compiled endpoint, build-time speedup or internal-PA theorem is claimed.

## Sources

Pinned Lean files: KSeedModel222.lean, KEqCodes222.lean, Kalmar.lean under Computability/BusyBeaver/Lean/BusyBeaver/ZFC at53269bcab1efc0f82d3022645bd7cf0c22d84959 (KSeedModel was independently checked unchanged from05d063). Local inherited sources and previous precise interface audit:research215_further_simplification/calculus/upstream/.
New notes inspected:research215_next_review/dr215__formalism__FORMALISM_NOTE.md and dr215__DR215__proofs__DR215_calibration.md. No downloaded research scripts were executed.
