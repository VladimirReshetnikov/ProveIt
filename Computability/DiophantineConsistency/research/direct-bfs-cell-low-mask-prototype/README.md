# Direct-BFS local low-mask no-carry

`DirectBFSCellDigitSupported.cellDigit_supported` bounds the nonzero digits of a direct-BFS cell to concrete low-mask support when the selected row is not forbidden. `DirectBFSBaseLowNoCarry.base_noCarry` then proves that the represented direct cell with dummy 0 is carry-disjoint from the concrete low mask. These are local ingredients for the halt-derived global packing; origin, pulses and the global high mask still need to be joined.

The guarded author check `observations/directbfscellowmask-attempt01/` exited 0 without diagnostics; all five exact axiom reports are `[propext, Classical.choice, Quot.sound]`. Direct imports were pinned and rechecked. Object `/tmp/direct-bfs-cellowmask-hij66dpd/DirectBFSCellLowMask.olean` has SHA-256 `23b75d5a284838ea365ef474fd47ae5471595b25777395b6c622622b788e0bea`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
