# PA194 addition output-existence supplier

`outputFoundationDerivation base` is a concrete current Foundation LK proof,
from the paid graph, intersection and separation assumptions, that each pair
of ordinal-domain inputs has a domain-valued output satisfying the upstream
`addResult` relation. It composes the checked addition-prefix totality proof
with the pinned upstream finite graph endpoint and output arguments.

`outputSupplier` pays those source assumptions and compiles the Foundation
proof to a finite PA194 calculus derivation. For any assignment `f`, it
assumes exactly `0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 3 + depth (∼prefixProperty base) ≤ z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (outputFoundationDerivation base) ≤ z`. Both budgets
refer to concrete Foundation derivations. The printed axiom reports are
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is output existence, not uniqueness or full correctness of interpreted
addition. Multiplication, the complete PA interpretation, PA-refutation
translation, machine nonhalting and internalization in PA/PRA remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-work/pa194-foundation-addition-output/check.sh`.
The script rebuilds the nested addition-totality prerequisites in tmpfs,
checks upstream pins and rejects `sorryAx` in printed axiom dependencies.
The standalone script completed successfully on 2026-11-15 using the retained
Lean 4.32 Foundation overlay, with no `sorryAx` in its audited reports. It
rebuilds the nested addition and induction source prerequisites but does not
authenticate the Foundation overlay itself or establish byte identity with
earlier staged objects.
