# Fixed-snapshot and workspace source drift

A read-only comparison after the recent origin merge found eight workspace source hashes differing from the isolated focused peer snapshot and four differing from the isolated full snapshot; `drift.json` records exact paths and hashes and `sources/` preserves the compared snapshots. Both builds read their separate immutable project-source trees, so workspace source changes do not invalidate them. Their results are about those fixed snapshots, not the later workspace. The named `ValidatorSeedTransitive222` is not in either audited source graph.

The focused snapshot/author inputs are in `../ha87-post-signed-frozen-peer/`; the full-source snapshot/inputs are in `../ha87-isolated-full-snapshot/`. Inherited HA/ZF/Foundation and transitive package ancestry retain their separate qualifications. This is a point-in-time drift observation, not a completed proof or a claim that no subsequent sources changed.
