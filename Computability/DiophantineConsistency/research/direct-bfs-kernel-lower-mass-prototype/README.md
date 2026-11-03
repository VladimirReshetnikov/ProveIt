# Direct lower-kernel mass bound

`DirectBFSKernelLowerMass.lower_le` proves `lower r ≤ 2^62*r^5495` for every natural `r≥1`, using the direct-family exact selector/copy masses. This is stronger than the checked `lower < r^5496` bound at `r=2^67` and is intended for a later high-mask padding estimate. It does not by itself establish a high-mask no-carry theorem.

Guarded author attempt `observations/directbfskernellowermass-attempt01/` exited 0 without diagnostics; both axiom reports are `[propext, Classical.choice, Quot.sound]`. Direct imports were pinned and rechecked. Object `/tmp/direct-bfs-kernellowermass-0e_pxd2v/DirectBFSKernelLowerMass.olean` has SHA-256 `71d7c229e2e8638aa28f2b790dec2bee64749c7579878b60d097e1b584949c67`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
