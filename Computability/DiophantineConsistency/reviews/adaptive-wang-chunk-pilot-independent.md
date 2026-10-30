# Independent Wang-table chunk pilot replay

The independent run `/tmp/adaptive-wang-chunk-pilot-hpsuaxk1` passed the extracted core and the first 128-row chunks for `GoodA`, `GoodB` and `GoodC`. All four source, object and full-log hashes match the author run. The original source pin and the canonical guard and provider-manifest hashes also match; canonical and package boundaries remain inherited.

The [16-file peer evidence manifest](adaptive-wang-chunk-pilot-independent-evidence/FILES.json) has SHA256 `30b6e421bea20e0f276a0405e152daf48c7838fe76cfc42c51e11c2a76e22f5c`. It preserves the peer driver, finalized state, generation metadata, original source snapshot, generated sources, logs and timings. This independently checks only the pilot's first 128 rows; it does not establish full coverage, an interface match or a current-source WangTable build. See the [author receipt](adaptive-wang-chunk-pilot-author.md).
