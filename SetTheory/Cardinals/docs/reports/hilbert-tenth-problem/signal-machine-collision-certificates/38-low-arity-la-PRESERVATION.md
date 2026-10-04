# Source preservation and concurrent release boundary

This task writes only the new `two-witness-tensor-compiler-20261004` packet and its new delivery archive/receipt. All prior arithmetic proof/audit directories and Reports 66–68 are read-only inputs to its actions. This document distinguishes the task's write boundary from changes made concurrently by a separate authorized release task.

## Original baseline

`evidence/source_before.json` records 912 file/directory entries from the predecessor compiler, its audit, accepted POWER12 packet, its audit, and Reports 66–68. Records include file hashes, bytes, modes, sizes, and nanosecond mtimes; access times are excluded because reading may change them.

The first new algebra run completed its mathematical assertions and then stopped at the final whole-baseline preservation assertion. Its authentic log is retained as `evidence/run_initial_preservation_interrupt.log`. Comparison found 17 changed entries, all in the concurrently active Report68 release tree. The README bytes changed; several files became read-only; directory mtimes also changed. The parent confirmed that the separate Report68 writer was legitimately finishing its reviews/status and sealing the release during this interval. No change is rolled back or hidden.

`evidence/concurrent_source_changes.json` retains the exact original/current entry differences. Reports66/67 and every frozen arithmetic dependency/audit match the original baseline. There is no claim of whole-interval Report68 preservation. The checker explicitly excludes that live tree from that original-baseline assertion; it does not silently replace the original baseline.

## Post-seal Report68 verification

The now-final Report68 manifest is pinned to the parent's final-release receipt:

- Final manifest SHA-256: 2a95eb0ba3f1f7bd2e53de2b0595d5b2439de11bc3c6b5925f15d63046f98493
- Final receipt SHA-256: d1781eeedb6f253e5e3a90551bd878c202d60ed4266619c7ceb61545d259240e

Fresh ordinary file/hash checks verify all 299 manifest payload files and 31 manifest directories, including hashes, byte sizes, modes and mtimes. `evidence/report68_receipt_pin.json` records those checks. No Report68 scientific checker or release tool is executed.

A new post-seal inventory contains 332 entries and is retained separately as `report68_postseal_before.json`. Its matching final read-only inventory is `report68_postseal_after.json`. This proves preservation only during that later interval. The original pre-seal snapshot, diff and interrupted-run log remain in the packet.

## Subsequent algebra evidence

The checker was extended to cover the separate one-witness appendix, its zero-witness closure classification, coefficient/support ceilings and d-input degree ledgers. The inspected augmented checker completed successfully; `run.log` and `results.json` record its final actual checks. The earlier successful augmented run before additional cost assertions is also retained. These are fresh algebra runs of this packet's own code, not executions of source scripts. Their purpose includes new mathematical checks and serialization of the completed evidence, not erasing the genuine preservation interruption.
