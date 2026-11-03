# Direct-BFS cell pulse identity

`DirectBFSCellPulseEquality.lean` proves that changing a direct-BFS cell's dummy bit from zero to one adds exactly `2^(67*1063)` and, for Boolean dummy values, each normalized cell is its zero-dummy cell plus that pulse. This is an IΣ₁-model arithmetic statement independent of graph zero or kernel identity. It is a packing-stability input, not yet calibrated rank or iPRA.

Accepted author run `observations/directbfscellpulseeq-attempt01/`: Lean and outer runner exited 0 without diagnostics; the two axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Output `/tmp/direct-bfs-cellpulseeq-99u53swb/DirectBFSCellPulseEquality.olean`, SHA-256 `d001ed95c02c91dbe3516e2134f3e78b2e55121d644f3e593f96a97601a18ff3`. All direct imports are pinned and rechecked. Project, package, dynamic, and historical source-to-object ancestry remain inherited limits; no independent Lean replay is claimed.
