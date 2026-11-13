# Complete high-digit run expansion at variable radix

`BFSHighRuns.expansion` in `BFSHighRunsV2.lean` expands the entire high-mask digit-run pattern at an arbitrary natural radix and arbitrary values for the three repeated-digit weights. Its right side is a weighted sum at the correct offsets, with three short geometric sums. It uses the generic [radix-run identities](../ten-positive-80-bfs-high-generic/README.md), so it does not evaluate the fixed huge coefficient.

The guarded accepted `observations/attempt02/` and enclosing tool session exited 0. Its source SHA-256 is `47880b6dfd52870835bf05a935be89f5148469e296d2445fca14545700f32319`; its output `/tmp/bfs-high-runs-95e4auty/BFSHighRunsV2.olean` has SHA-256 `9864ee2d0d90c6b6cc5db02b9cbf205f712e1e6b3e80855b68a8a96a3ffc7d3f`. Attempt01 failed on a normalization goal and warnings; its source and runner are retained with the observation. The accepted runner pins its direct generic-run provider and selected historical inputs. Full source/object, package-transitive and dynamic ancestry remains inherited; no independent Lean replay is claimed.

This is a generic expansion, not yet a formal equality between the exact interval-sum formula in the PDF and `CompactSymbolicPorts.highNat`, a fixed-port iPRA specialization, or a file-semantics theorem.
