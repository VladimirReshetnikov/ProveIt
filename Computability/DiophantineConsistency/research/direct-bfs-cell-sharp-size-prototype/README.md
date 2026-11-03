# Sharper direct-cell size bound

`DirectBFSCellSharpSize.packedCell_lt_twice_top` proves `packedCell a d < 2*Exp.exp(67*3296)` for a non-forbidden row and Boolean dummy, by combining the checked support bound with Booleanity of the highest digit. This supports the high-padding size argument but does not itself prove high-mask no-carry.

The guarded author check `observations/directbfscellsharp-attempt01/` exited 0 without diagnostics; its axiom report is `[propext, Classical.choice, Quot.sound]`. Direct imports were pinned and rechecked. Object `/tmp/direct-bfs-cellsharp-bdihldh8/DirectBFSCellSharpSize.olean` has SHA-256 `1b7ac53da57ecdf38116267d37d035c2d10310c1308afe07cd3705ea690a1422`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
