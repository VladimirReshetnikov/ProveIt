# PA194 Kuratowski-pair existence supplier

`kuratowskiFoundationDerivation a b` is a concrete current Foundation LK
proof that the paid exact graph context supplies a Kuratowski-pair witness
for source variable labels `a,b`. It is built from the pinned upstream
finite pair and adjunction proof templates, adapted to current Foundation.
The result asserts existence of a witness; it does not assume extensionality
or a canonical choice of pair.

`kuratowskiSupplier` composes that Foundation proof with the paid PA194
graph-context suppliers and compiler. For any assignment `f`, it constructs
a finite PA194 proof of the translated pair-existence formula, assuming
`0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (kuratowskiFoundationDerivation a b) ≤ z`.
Both budgets refer to explicitly constructed Foundation derivations. Printed
axiom dependencies are `[propext, Classical.choice, Quot.sound]`, without
`sorryAx`.

This is one ordinary Lean building block toward the arithmetic source
interpretation. It does not by itself prove the graph, addition,
multiplication, induction or PA-refutation translations, machine nonhalting,
or internalization in PA/PRA.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-pair/check.sh`. It
rebuilds the raw-successor prerequisite chain in tmpfs, checks and builds
the graph-context module in the same overlay, checks upstream pins and
rejects `sorryAx` in printed axiom dependencies. The five new modules have
passed an overlay check; the full standalone script has not yet completed.
