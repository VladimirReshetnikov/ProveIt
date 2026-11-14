# PA194 graph-extension supplier

`extensionFoundationDerivation g a b` is a concrete current Foundation LK
proof that the paid exact graph context supplies an extension of graph `g`
containing a Kuratowski entry for `(a,b)` while preserving existing edges.
The finite source proof adapts the pinned upstream graph-entry and extension
arguments to current Foundation. It does not claim exact classification of
all edges of the extended graph.

`extensionSupplier` composes that Foundation proof with the paid PA194 graph
context and compiler. For any assignment `f`, it constructs a finite PA194
proof of the translated extension-existence formula, assuming `0 < lo`,
`∀ i, f i < lo`, `lo + 6 < z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (extensionFoundationDerivation g a b) ≤ z`.
Both budgets refer to explicitly constructed Foundation derivations. Printed
axiom dependencies are `[propext, Classical.choice, Quot.sound]`, without
`sorryAx`.

This is an ordinary Lean building block for the arithmetic interpretation;
the exact graph, addition, multiplication, induction and PA-refutation
translations, machine nonhalting, and internalization in PA/PRA remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-graph-extension/check.sh`.
The script rebuilds the nested pair prerequisites in tmpfs, checks upstream
pins and rejects `sorryAx` in printed axiom dependencies. The three new
modules have passed an overlay check; the full standalone script has not yet
completed.
