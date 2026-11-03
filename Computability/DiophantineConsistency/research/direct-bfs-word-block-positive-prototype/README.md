# Direct-BFS cell and block positivity

`DirectBFSWordBlockPositive.packedCell_pos` proves a normalized direct-cell's selector gives positive cell value for any bounded row. `block_pos` uses a temporal predecessor to prove every transport block is positive for any direct-BFS local word, arbitrary normalized dummy family, radix and kernel. This discharges the positive-origin block condition in the conditional packing interface; it does not prove high-mask no-carry.

Guarded author attempt `observations/directbfsblockpositive-attempt01/` exited 0 without diagnostics; both axiom reports are `[propext, Classical.choice, Quot.sound]`. Direct imports were pinned and rechecked. Object `/tmp/direct-bfs-blockpositive-sdmxpakd/DirectBFSWordBlockPositive.olean` has SHA-256 `a0717f51a636c98831113f6f9cea53aca4181bc88f59f063f21d6ace8e325cf1`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
