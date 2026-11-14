# PA194 exact graph-extension supplier

`exactFoundationDerivation g a b` is a concrete current Foundation LK proof,
adapted from the pinned upstream finite pair-decoding and graph-classification
arguments, that the six paid graph-context assumptions imply an exact
extension exists. Its edges are precisely the old graph's edges together
with those whose endpoints equal `a,b` in the source equality relation. It
uses witness-based pair representations and does not assume extensionality
or canonical representatives.

`exactExtensionSupplier` composes this Foundation proof with the paid
PA194 graph-context suppliers and current Foundation LK compiler. For any
assignment `f`, it constructs a finite PA194 proof of the translated exact
extension formula, assuming `0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (exactFoundationDerivation g a b) ≤ z`. Both budgets
refer to explicitly constructed Foundation derivations. Printed axiom
reports are `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

This is an ordinary Lean component of the arithmetic interpretation. It
does not yet prove addition, multiplication or induction, translate PA
refutations, establish machine nonhalting, or internalize the compiler in
PA/PRA.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-graph-exact/check.sh`.
The script rebuilds the nested graph-extension chain in tmpfs, checks and
builds the needed successor-closure prefix in the same overlay, verifies
upstream pins and rejects `sorryAx` in printed axiom dependencies. The new
modules have passed an overlay check; the full standalone script has not yet
completed.
