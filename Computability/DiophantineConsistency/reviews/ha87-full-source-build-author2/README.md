# Stopped full project-source author build after source drift

The run `/tmp/ha87-full-source-vkynsi51` was externally interrupted after its current Lean subprocess had exited, because five merged validator sources no longer matched its frozen source snapshot. The exact terminal state reports `FAILED` / `KeyboardInterrupt`; `observed-source-drift.json` records the independently observed before/after hashes. It has 72 verified completed module records. The module active at interruption is unverified and is not included in that count. Driver, state, exact source snapshots and complete logs for recorded attempts are retained.

This is not a completed proof or an independent replay. A new graph must authenticate current sources and direct dependency hashes before reusing any verified prefix. Historical/package provenance remains as stated in the driver and source plan.
