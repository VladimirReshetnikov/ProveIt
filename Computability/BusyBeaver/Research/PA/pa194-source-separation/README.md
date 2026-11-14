# PA194 source separation supplier

The modules adapt the pinned PA196 separation-schema, relocation and
source-supplier arguments to the independently checked PA194 calculus.
`separationSupplier` constructs a finite PA194 derivation of the translated
source separation formula for any source semiformula property and any free
parameter assignment `f` with `0 < lo`, `f i < lo` for every `i`, and
`lo + 3 + depth p ≤ z`.
Its printed axiom dependencies are `propext`, `Classical.choice` and
`Quot.sound`, with no `sorryAx`. The weak adjunction supplier also checks
for every assignment `f` under `lo + 3 < z`.

This is one supplier in a source-theory translation. It does not establish
that PA proofs translate to this theory, that PA is consistent, or that the
compiler and its reduction are formalized within PA/PRA. The source files
are adapted from the pinned upstream files; their hashes identify the source,
not a claim that the two Foundation versions are definitionally equal.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation object directory and run `bash
Computability/BusyBeaver/Research/PA/pa194-source-separation/check.sh`.
It rebuilds the complete source-LK prerequisite chain in tmpfs, checks
upstream hashes and rejects `sorryAx` in printed theorem dependencies.
The complete nested separation check passed, including all four modules and
their prerequisites.
