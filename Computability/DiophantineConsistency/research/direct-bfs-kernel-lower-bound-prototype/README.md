# Direct-BFS kernel split and lower-part bound

`DirectBFSKernelLowerBound.kernel_split` expresses the direct kernel as its explicit lower family plus the top radix term `r^8807*r^42`. `lower_lt` proves the lower family is less than `r^5496` for natural `r≥2^67`. The proof uses the checked selector/copy masses and bounds each lower power by `r^5495`. This is an ingredient toward identifying the high half of the kernel times a small cell; it does not by itself establish a high-mask packing field.

Guarded author attempt `observations/directbfskernellower-attempt01/` exited 0 without diagnostics; both exact axiom reports are `[propext, Classical.choice, Quot.sound]`. Direct imports were pinned and rechecked. Object `/tmp/direct-bfs-kernellower-p3eup005/DirectBFSKernelLowerBound.olean` has SHA-256 `770094c18d60ec28900d05acfe43b428e429c87d19d8200cd4268ed35d0dfd06`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
