# Isolated full-source fresh prefix checkpoint

A read-only checkpoint of live `/tmp/ha87-full-transitive-p3xt6wra` captured 263 verified project rows, all compiled from the fixed source tree with zero prefix reuse. It adds 133 rows to `../ha87-isolated-full-prefix/`; their complete logs and the exact RUNNING state are included, and their output objects/logs were rehashed against that state. The live run may have advanced since capture. This is prefix evidence, not a terminal proof PASS or an independent replay.

The complete source manifest, source deltas, Lake configuration and isolated audit are in `../ha87-isolated-full-snapshot/`. Direct external package objects are guarded, but package-transitive source/object ancestry remains inherited. The run concerns its fixed project snapshot, not later workspace changes.
