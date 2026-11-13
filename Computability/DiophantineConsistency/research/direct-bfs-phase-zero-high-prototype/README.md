# Direct-BFS phase-zero high-mask safety

`DirectBFSPhaseZeroHigh.phase_zero_noCarry` proves that every normalized transport block of a direct-BFS local word is carry-disjoint from the high-mask digit at phase zero. The proof uses the direct kernel's radix divisibility, its high-product split and small-cell bound. It covers one phase only; the other high-mask phase classes and the all-index no-carry theorem remain open.

Guarded author attempt `observations/directbfsphasezero-attempt01/` exited 0 without diagnostics and reports `[propext, Classical.choice, Quot.sound]`. Direct imports were pinned and rechecked. Object `/tmp/direct-bfs-phasezero-s3imda6v/DirectBFSPhaseZeroHigh.olean` has SHA-256 `6fc7c28345e6f7e1cad4175e28b41088f94b60ef9aec5989d610bcf0dcd92389`. Inherited project/package/dynamic and source-object ancestry remains unverified; no independent Lean replay is claimed.
