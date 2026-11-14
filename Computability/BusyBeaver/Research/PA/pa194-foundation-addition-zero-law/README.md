# PA194 zero-input addition-result law

`zeroLawFoundationDerivation x base out` is a concrete current Foundation LK
proof, from the six paid exact-graph assumptions, that if source input `x`
satisfies the zero formula and `addResult x base out` holds, then `out`
equals `base` in the source equality relation. It adapts the pinned upstream
zero-result proof without assuming canonical zero representatives or graph
choices.

`zeroLawSupplier` pays the graph assumptions and compiles the Foundation
proof to a finite PA194 calculus derivation. For any assignment `f`, it
assumes exactly `0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (zeroLawFoundationDerivation x base out) ≤ z`.
Both budgets refer to concrete Foundation derivations. Printed axiom reports
are `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is one ordinary Lean source addition-result law, not full addition
coherence, all PA addition axioms, multiplication, a PA-refutation
translation, machine nonhalting, or internalization in PA/PRA.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-addition-zero-law/check.sh`.
The script rebuilds the nested addition-step prerequisites in tmpfs, checks
upstream pins and rejects `sorryAx` in printed axiom dependencies. The new
modules have passed an overlay check; the full standalone script has not yet
completed.
