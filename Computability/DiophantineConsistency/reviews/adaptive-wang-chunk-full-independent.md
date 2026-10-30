# Independent full Wang predicate-chunk replay

The independent run `/tmp/adaptive-wang-chunk-full-042v1clo` passed the extracted core, all 24 finite row chunks and the take/drop recombination module. All 26 source, object and full-log hashes match the author run; the pinned original-source, canonical-guard and provider-manifest hashes also match. The canonical and package boundaries remain inherited.

The [82-file peer evidence manifest](adaptive-wang-chunk-full-independent-evidence/FILES.json) has SHA256 `c7c1e142f9e6f1a9a224b15e5a6b7cb9edff070f40ac8b6d2b3040e31c2b8983`. It preserves the peer driver, finalized state, generation metadata, original source snapshot, all generated source snapshots, full logs and timings. This is a replay of the private chunk proof only: it does not rebuild the original WangTable module or establish an all-export interface match. See the [author receipt](adaptive-wang-chunk-full-author.md).
