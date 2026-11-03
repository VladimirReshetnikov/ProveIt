# Trace75 / BFS provider overlap preflight

The proposed direct-BFS carry client would combine the checked trace75
fixed-congruence chain with `DirectBFSBandCarry`. The current trace75
`DiophantineConsistency` overlay and the coherent BFS union share 997
`.olean` paths, of which five differ in bytes. `compare.py` independently
records both paths, resolved targets and SHA-256 hashes for each mismatch,
plus presence and hashes of companion files. It pins the coherent BFS replay
receipt and rechecks the compared inputs after reading them.

`observations/compare-attempt01/result.json` SHA-256
`7466cf187de963c0ccc2c112d7b8dc77dcddaf0ae3fda47f76e8ad9d54cf64a8`
lists the five: `ModelRatioBounds`, `ArithmeticNegativeNorms`,
`ArithmeticCarrierRadix2011`, `ArithmeticWindowInterface`, and
`ArithmeticCarrierSoundness2011`. In particular, the trace75 overlay has
historical `ModelRatioBounds` `fcf4152e…` and the fresh BFS union has
`8ba17e0b…`. Historical producer drift for the former is already known.

This compares current overlapping namespace files. It does not show that
any mismatch is in either root's serialized ancestry, determine a safe
search order, replay any Lean theorem, establish transitive/package
provenance, or prove a machine/iPRA equivalence. The carry client remains
held pending a selected-ancestry scan and provider-coherence analysis.

## Selected serialized ancestry

The independently reviewed `scan-v2.py` constructs a **hypothetical**
search order from the recorded trace75 fixed-congruence path, followed by
the coherent BFS union before the project library. It traverses the two
specified roots, resolves each project module at the first existing object,
rejects dangling shadows, snapshots all selected object/companion paths and
hashes, and re-resolves/rechecks them after the scan. It reuses BFS replay
header records only when the selected `.olean` hash matches; all other
selected project headers are read in guarded Lean batches. The BFS root's
selected ancestry and companion hashes are compared with that replay.

`observations/scan-attempt01/result.json` has SHA-256
`e27f1cb8694aab43a1023abcce95f7fbc7846d4860dac4b96046391da3dd1e8d`.
The outer receipt `observations/outer-attempt01/terminal.json` has SHA-256
`5a916a82f6bf12f2102f00d48183229c669aeda6fc760edeb4df670c17b468c7`
and records actual child exit 0 and unchanged scanner hash. The scan found
248 distinct selected project objects and 28 outside objects, using 11
reader batches and 192 exact-hash captured-header reuses.

The `DirectBFSBandCarry` subtree has 46 selected project objects, none of
the five mismatch names, and no object or companion conflict with the BFS
replay capture. `Trace75FixedCongruence` has 208 selected project objects;
its serialized ancestry includes historical `ModelRatioBounds`
(`fcf4152e…`) and `ArithmeticNegativeNorms` (`ecdcffd5…`), while the
other three mismatch names are absent. The complete paths, hashes, direct
headers, outside boundary and ancestry lists are in the result. The two
root objects are pinned as `c0f5362c…` and `e585f2a5…`, respectively.

This is evidence for the selected current path, not a checked carry join,
a historical compiler-input replay for the trace75 chain, or a full
outside/package/dynamic ancestry audit. In particular, the earlier
producer-time drift of historical `ModelRatioBounds` remains unresolved;
coherent rebuilding against the fresh provider is still needed. An
[independent post-scan audit](../../reviews/trace75-bfs-selected-ancestry-independent/README.md)
checks both root reachability, recorded first selections and companions without
replaying Lean or authenticating the remaining historical ancestry.
