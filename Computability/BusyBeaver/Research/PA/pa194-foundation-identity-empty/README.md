# PA194 identity graph for a zero object

`emptyIdentityFoundationDerivation a` is a concrete current Foundation LK
proof, with no nonlogical source assumptions, that a source zero object
admits its identity graph. It adapts the pinned upstream witness-based
order-isomorphism syntax and empty-identity argument without assuming
extensionality or canonical representatives.

`emptyIdentitySupplier` compiles that proof to a finite PA194 calculus
proof of the translated implication. For any assignment `f`, it assumes
exactly `0 < lo`, `∀ i, f i < lo`, and
`lo + foundationBudget (emptyIdentityFoundationDerivation a) ≤ z`; the
budget refers to the constructed Foundation proof. Its printed axiom report
is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is the empty-domain identity case only. General identity and
isomorphism, addition coherence and full PA interpretation, PA-refutation
translation, machine nonhalting and internalization in PA/PRA remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-identity-empty/check.sh`.
The script rebuilds the nested zero-prefix prerequisites in tmpfs, checks
upstream pins and rejects `sorryAx` in the printed axiom dependencies. The
new modules have passed an overlay check; the full standalone script has not
yet completed.
