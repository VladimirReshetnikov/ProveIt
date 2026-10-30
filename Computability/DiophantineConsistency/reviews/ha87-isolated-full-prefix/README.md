# Isolated full-source fresh prefix snapshot

A read-only checkpoint of live build `/tmp/ha87-full-transitive-p3xt6wra` captured 130 verified rows, all compiled from the fixed project source tree with zero prefix reuse. The included state is the exact RUNNING state at capture; each included log and output object was rehashed against its record. The live build may have advanced since this snapshot. This is a prefix checkpoint, not a terminal build PASS or an independent replay.

The complete 729-source snapshot manifest, source deltas, frozen driver/Lake configuration and isolated audit are in `../ha87-isolated-full-snapshot/`. The full build's direct external package objects are guarded, but package-transitive object/source ancestry remains inherited. Its result concerns the fixed project snapshot, not later workspace changes.
