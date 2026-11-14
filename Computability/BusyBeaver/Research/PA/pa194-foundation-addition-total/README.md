# PA194 addition-prefix totality supplier

`totalFoundationDerivation base` is a concrete current Foundation LK proof,
from the paid graph, intersection and separation assumptions, of the source
formula `domain base → ∀ a, domain a → addPrefixExists a base`. It adapts the
pinned upstream proof that composes the zero-prefix base, successor step and
uniform ordinal-source induction.

`totalSupplier` pays all its source assumptions with checked PA194 suppliers
and compiles the constructed Foundation proof. For any assignment `f`, it
constructs a finite PA194 proof of the translated formula, assuming exactly
`0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 3 + depth (∼prefixProperty base) ≤ z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (totalFoundationDerivation base) ≤ z`. Both budgets
refer to concrete Foundation derivations. Printed axiom reports are
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is source addition-prefix existence for domain inputs, in ordinary Lean.
It does not yet establish interpreted addition output/correctness,
multiplication, the complete PA interpretation or PA-refutation translation,
machine nonhalting, or internalization in PA/PRA.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-addition-total/check.sh`.
The script rebuilds the nested induction prerequisites in tmpfs, checks the
upstream pins and rejects `sorryAx` in printed axiom dependencies. The new
modules have passed an overlay check; the full standalone script has not yet
completed.
