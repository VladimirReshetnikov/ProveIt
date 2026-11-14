# PA194 ordinal-domain successor closure

`domainSuccessorFoundationDerivation a` is an actual current Foundation LK
proof, adapted from the pinned upstream finite proof, that equality,
intersection and exact adjunction imply `domain a → ∃ b, domain b ∧
successor a b`. It verifies the source-domain transitivity, member
transitivity and linearity, internal extrema, and member irreflexivity.

`domainSuccessorSupplier` composes this constructed derivation with the
already checked six PA194 source suppliers and the current Foundation LK
compiler. For source term `a` and assignment `f`, it constructs a finite
PA194 proof of the translated closure formula. It assumes exactly `0 < lo`,
`∀ i, f i < lo`, `lo + 6 < z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (domainSuccessorFoundationDerivation a) ≤ z`.
Both budgets refer to concrete constructed Foundation derivations; no source
proof or axiom-supplier premise remains. The printed axiom reports are
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is one ordinary Lean component of the PA interpretation. Addition,
multiplication, induction, PA-refutation translation, machine nonhalting and
internalization in PA/PRA remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-successor/check.sh`.
The script rebuilds the nested raw-successor prerequisites in tmpfs, checks
the pinned source files and rejects `sorryAx` in printed axiom dependencies.
The new modules have passed an overlay check; the full standalone script has
not yet completed.
