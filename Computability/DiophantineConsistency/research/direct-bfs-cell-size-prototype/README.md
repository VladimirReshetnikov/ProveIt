# Sharp support-based direct-cell bound

`DirectBFSCellSizeBound.packedCell_lt_support` proves that a direct-BFS packed cell with non-forbidden row and Boolean dummy is smaller than `Exp.exp (67*3297)` in every IΣ₁ model. The proof uses the actual concrete low-mask support to show every later allocated digit is zero. This is a quantitative input to a future direct-kernel product bound; it does not itself prove the `PackingInput` product field.

Guarded author attempt `observations/directbfscellsize-attempt01/` exited 0 without diagnostics; all three axiom reports are `[propext, Classical.choice, Quot.sound]`. Direct imports were pinned and rechecked. Object `/tmp/direct-bfs-cellsize-i4yzl_mv/DirectBFSCellSizeBound.olean` has SHA-256 `298d3daf4130c1d9db8c7e537a53314b19be3092cfb670d87f01988258aaa9a0`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
