# Later upstream K217 changes

The merge of `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95` retains upstream's
`ab6ceabe32` AX macro-word refactor and `6d9800d1ca` boundary-state enumerator
refactor. The normal merge preserves both the phase15 documentation and the
later K217 edits. The four changed Lean modules are outside the 199-project
K215 primary/compatibility union; every checked K215 source hash remains exact.

The AX development composes previously named macro contracts, checks the
literal macro word with kernel decision, and identifies its effect with the
existing enumerator step. The enumerator now states completeness from an
arbitrary boundary index, choosing one cofinal reset candidate for every
working payload. Its equivalence retains the derivability invariant. SeedDom
is the seed instance, and unused zero-start wrappers are removed.

These upstream sources and their diff were read as code. Their producer
changes are preserved without execution. No new local K217 compiler acceptance
or runtime replay is claimed by this merge; the phase15 checks concern the
unchanged exact K215 construction. Source194's older EnumDom comparison is
historical after this refactor and must be rebased before future adoption.

The [merge map](map.json) binds all eight merged files, including the retired
EnumDom generator. No current K215 source, native table, proof packet, or
internal PA/ZFC claim changes.
