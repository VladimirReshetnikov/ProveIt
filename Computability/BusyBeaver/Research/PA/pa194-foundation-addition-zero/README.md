# PA194 zero-input addition-prefix supplier

`zeroPrefixFoundationDerivation a b` is a constructed current Foundation LK
proof, from the six paid graph-context assumptions, of the upstream source
formula `zero a ∧ domain b → addPrefixExists a b`. Its finite proof adapts
the pinned formula-equality, trace-graph, point-graph and zero-prefix
arguments to current Foundation and the checked natural-deduction interface.

`zeroPrefixSupplier` composes that derivation with the paid PA194 graph
context and current Foundation LK compiler. For any assignment `f`, it
constructs a finite PA194 proof of the translated formula, assuming exactly
`0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (zeroPrefixFoundationDerivation a b) ≤ z`.
Both budgets refer to concrete Foundation derivations. Printed axiom reports
are `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is the zero-input prefix-existence case only. Full addition,
multiplication, induction and PA-refutation translations, machine nonhalting,
and internalization in PA/PRA remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-addition-zero/check.sh`.
The script rebuilds the nested exact-graph prerequisites in tmpfs, checks the
upstream pins and rejects `sorryAx` in printed axiom dependencies. The new
modules have passed an overlay check; the full standalone script has not yet
completed.
