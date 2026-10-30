# Equality/R2 source drift and new rebases

Two successive merges changed guarded sources `ValidatorEqualityCore222` and `R2Neg`. The focused run `/tmp/ha87-focused-validator-rebase-qhd75h_b` stopped with FAILED/KeyboardInterrupt while authenticating its historical boundary, before any compiled records. The full-source run `/tmp/ha87-full-source-oqfx8o0n` stopped with FAILED/KeyboardInterrupt at `Table253` once its Lean child exited; 117 rows were verified, 113 reused and four new. This was an external stop, not a guard failure. The unrelated WangTable worker was untouched.

This packet preserves terminal states, four new full logs, before/after snapshots and hashes, and the focused rebase driver and graph. Previous source snapshots, logs and ancestry are referenced in `../ha87-unbounded-assembly-rebase/` and earlier packets. The updated focused graph records the new equality-core import; recomputing reachability left the HA/model/normalization node sets unchanged. The R2Neg imports did not change.

The subsequent focused `/tmp/ha87-focused-validator-rebase-9aq3ukbn` and full `/tmp/ha87-full-source-kbnfl6iv` author rebases later stopped for source drift; their terminal states are in `../ha87-zf-fallback-failure-and-rebase/`. The focused inherited HA and package provenance remains explicitly qualified.
