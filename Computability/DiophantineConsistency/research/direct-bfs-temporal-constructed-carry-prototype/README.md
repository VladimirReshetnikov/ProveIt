# Direct-BFS temporal product carry

`DirectBFSTemporalConstructedCarry.temporal_product_carry` combines the checked direct symbolic-product carry input with the actual temporal rotation. Given a bounded source and digit cap, it supplies the exact carry input for the cyclic remainder of `(K+2^e)*C`, without a separate temporal bound premise. It does not yet derive high-mask safety or a halt→graph packing.

Guarded author attempt `observations/directbfstemporalcarry-attempt01/` exited 0 without diagnostics; its axiom report is `[propext, Classical.choice, Quot.sound]`. Direct imports were explicitly pinned and rechecked. Object `/tmp/direct-bfs-temporalcarry-ajxlgsqj/DirectBFSTemporalConstructedCarry.olean` has SHA-256 `7fb367ee3005ebb4542986a124f865d8a7d8de3698e74dd7fe6099cd1a06e6e5`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
