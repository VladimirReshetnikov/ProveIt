# PA194 raw successor supplier

`rawSuccessorFoundationDerivation a` is an actual current Foundation LK
proof that exact adjunction implies existence of a successor of the source
term `a`. `rawSuccessorSupplier` composes this derivation with the checked
PA194 adjunction supplier and Foundation LK compiler to construct a finite
PA194 proof of the translated successor-existence formula.

For assignment `f`, the supplier assumes exactly `0 < lo`, `∀ i, f i < lo`,
`lo + 6 < z`, `lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`,
and `lo + foundationBudget (rawSuccessorFoundationDerivation a) ≤ z`.
Both budgets refer to explicitly constructed Foundation derivations; no
source-proof premise remains. Its printed axiom dependencies are
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This proves raw successor existence; closure of the ordinal domain under
successor, the remaining PA interpretation, PA-refutation translation, and
internalization in PA/PRA remain open. The source proof adapts the pinned
upstream raw-successor template to current Foundation.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-raw-successor/check.sh`.
The script rebuilds the nested ordinal prerequisites in tmpfs, checks the
upstream pin and rejects `sorryAx` in the printed axiom dependencies. The
new modules have passed an overlay check; the full standalone script has not
yet completed.
