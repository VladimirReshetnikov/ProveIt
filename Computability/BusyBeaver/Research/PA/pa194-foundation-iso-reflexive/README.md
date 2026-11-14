# PA194 order-isomorphism reflexivity

`orderIsoReflexivityFoundationDerivation` is a concrete current Foundation
LK proof that every source ordinal-domain object is order-isomorphic to
itself. It adapts the pinned upstream proof that a witnessed identity graph
satisfies the seven explicit order-bijection clauses; no extensionality or
canonical graph choice is assumed.

`orderIsoReflexivitySupplier` pays the checked source assumptions and
compiles that proof to a finite PA194 calculus derivation. For any assignment
`f`, it assumes exactly `0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 3 + depth (∼identityProperty) ≤ z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget orderIsoReflexivityFoundationDerivation ≤ z`.
Both budgets refer to concrete Foundation derivations. Printed axiom reports
are `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This ordinary Lean result is reflexivity only. Isomorphism symmetry and
transitivity, addition coherence and full PA interpretation, PA-refutation
translation, machine nonhalting and internalization in PA/PRA remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-iso-reflexive/check.sh`.
The script rebuilds the nested identity prerequisites in tmpfs, verifies
upstream source pins and rejects `sorryAx` in printed axiom dependencies. The
new modules have passed an overlay check; the full standalone script has not
yet completed.
