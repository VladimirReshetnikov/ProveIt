# PA194 source intersection supplier

`intersectionAxiomSupplier` gives a finite PA194 calculus proof of the
translated fixed universally closed intersection axiom, as an instance of the
already checked arbitrary-property separation supplier. It assumes exactly
`0 < lo` and `lo + 4 ≤ z`, for any assignment `f`. Its reported Lean axioms
are `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This adapts the pinned upstream source definition and supplier to current
Foundation; it is one component of a source-theory translation, not a PA
refutation or an internal PA/PRA proof. The full source interpretation and
machine reduction remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-source-intersection/check.sh`.
It rebuilds the nested source-context chain in tmpfs, verifies upstream
hashes and rejects `sorryAx` in the printed theorem dependencies. The module
has been checked against rebuilt prerequisite overlays; the full standalone
script has not yet completed.
