# PA194 identity graphs on the ordinal source domain

`identityFoundationDerivation` is a concrete current Foundation LK proof
that every source ordinal-domain object has an identity graph. It adapts the
pinned upstream finite entry, successor-witness and ordinal-induction
arguments, using ordinary equality, empty-set existence, adjunction,
intersection and separation of the negated identity property. No
extensionality or canonical graph choice is assumed.

`identitySupplier` pays all source assumptions with already checked PA194
suppliers and compiles the Foundation proof to a finite PA194 derivation.
For any assignment `f`, it assumes exactly `0 < lo`, `∀ i, f i < lo`,
`lo + 6 < z`, `lo + 3 + depth (∼identityProperty) ≤ z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget identityFoundationDerivation ≤ z`. Both budgets
refer to concrete Foundation derivations. Printed axiom reports are
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is an ordinary Lean source-theory result. General order-isomorphism
coherence, addition correctness, the complete PA interpretation,
PA-refutation translation, machine nonhalting and internalization in PA/PRA
remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-identity/check.sh`.
The script rebuilds the nested induction prerequisites in tmpfs, builds the
needed pinned empty-identity modules in the same overlay, checks source pins
and rejects `sorryAx` in printed axiom dependencies. The new modules have
passed an overlay check; the full standalone script has not yet completed.
