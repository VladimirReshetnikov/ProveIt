# PA194 graph-context supplier and compiler

`graphContextSupplier` supplies translated finite PA194 proofs for each of
the six source assumptions used by the pinned upstream exact graph
construction: empty-set existence, exact adjunction, and equality
reflexivity, symmetry, transitivity and membership congruence. For any
assignment `f`, it assumes `0 < lo`, `lo + 6 < z`, and
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`.

`compileGraphContext` composes these paid premises with the current
Foundation LK compiler. Given an explicit Foundation derivation `d` of a
source formula `q` from that context, `∀ i, f i < lo`, and
`lo + foundationBudget d ≤ z`, it constructs a finite PA194 proof of the
translation of `q`. It does not yet construct the particular graph,
addition or multiplication derivations, nor internalize this compiler in
PA/PRA. Both printed axiom reports are `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx`.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation object directory and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-graph-context/check.sh`.
It rebuilds the nested Foundation-adjunction chain in tmpfs, verifies the
upstream source pins and rejects `sorryAx` in printed axiom dependencies.
The module has passed an overlay check; the full standalone script has not
yet completed.
