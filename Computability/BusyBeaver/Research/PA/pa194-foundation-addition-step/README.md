# PA194 addition-prefix successor step

`stepFoundationDerivation top u base` is a constructed current Foundation LK
proof that the six paid exact-graph assumptions and the fixed intersection
axiom imply the source formula
`domain top ∧ successor top u ∧ addPrefixExists top base → addPrefixExists u base`.
It adapts the pinned upstream finite graph-extension, recurrence and prefix
step arguments to the current Foundation calculus.

`stepSupplier` composes that proof with all seven paid PA194 source
suppliers and the current Foundation LK compiler. For any assignment `f`, it
constructs a finite PA194 proof of the translated implication, assuming
exactly `0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (stepFoundationDerivation top u base) ≤ z`. Both
budgets refer to concrete Foundation derivations. Printed axiom reports are
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is one successor step for addition-prefix existence. Source induction,
full addition totality and correctness, multiplication, PA-refutation
translation, machine nonhalting, and internalization in PA/PRA remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-addition-step/check.sh`.
The script rebuilds the nested zero-prefix prerequisites in tmpfs, compiles
the remaining pinned successor-closure modules in the same overlay, checks
upstream pins and rejects `sorryAx` in printed axiom dependencies. The new
modules have passed an overlay check; the full standalone script has not yet
completed.
