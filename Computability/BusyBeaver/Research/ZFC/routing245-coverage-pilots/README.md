# Routing245 coverage pilots

Ten Lean modules pass 17 named theorem probes and 31 typed callers, with
zero warnings. Seven individual leaves exercise deep paths, long bit runs,
both decrement branches, and the halt instruction. Three complete subtrees
check 90 leaves and 117 guarded cases against the actual imported decoder
tree and its full path context.

The leaf and subtree families overlap; their coverage counts must not be
added. These pilots do not prove complete acceptance of all 8,391 guarded
cases. The full coverage proof reuses the three subtree modules directly.

Each source/audit pair shares a 120-second budget with one thread, 4,096 MiB,
default proof limits, and unchanged checker fuel 4,000. The largest measured
subtree took 31.023 seconds for its source and 0.627 seconds for its audit.
The [publication manifest](publication.json) identifies every actual run;
[history](history.json) preserves the original sources, audits, preparations,
guards, logs, generated metadata, and reviews as lossless UTF-8 blobs.
[The exact publication map](publication-map.json) records the installed files.
Compiled objects are excluded and no clean-checkout rebuild is claimed.

Attribution and the machine specification follow the
[candidate notice](../candidate-routing245/README.md). These are proofs about
the original 245-state candidate, with no stronger theory substituted.
