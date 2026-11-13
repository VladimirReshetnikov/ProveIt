# Lower-kernel mass bound on the existing split definition

`DirectBFSKernelLowerMassAlias.lower_le` reproves the checked mass estimate `lower r ≤ 2^62*r^5495` for `r≥1` directly on the `DirectBFSKernelLowerBound.lower` definition used by the high-product split. This avoids unfolding and comparing two huge instantiated kernel sums when composing them in a model. It does not itself prove high-padding safety.

Guarded author attempt `observations/directbfskernellowermassalias-attempt01/` exited 0 without diagnostics; both axiom reports are `[propext, Classical.choice, Quot.sound]`. Direct imports were pinned and rechecked. Object `/tmp/direct-bfs-kernellowermassalias-l6qen69x/DirectBFSKernelLowerMassAlias.olean` has SHA-256 `0bc39dae81e46387dab2c52d0f57af189934ee67bc4ae38a5ae8efe617ef545c`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
