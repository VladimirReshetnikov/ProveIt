# Adaptive clients after the HalfBinomialSandwich update

An author replay passed the 18-module affected suffix from the updated `ArithmeticHalfBinomialSandwich` through HalfBinomial, the adaptive population and actual-zero window clients, and six reverse-construction clients, with their checks. All rebuilt source snapshots and inherited provider files were reauthenticated at the end. This is a suffix build, not a fresh build of the full transitive closure. Independent replay at `/tmp/adaptive13-sandwich-postmerge-8tly07ke` passed with all 18 source, object and complete-log hashes matching the author run.

The Sandwich update changes the proof body of `base_eq'` to use additive cancellation and the existing `base_eq`; its statement is unchanged. The inherited base is the preceding 17-module author attempt: all 17 modules compiled, but its final source check failed because that attempt used the earlier Sandwich source. The replay explicitly authenticates that failed attempt's recorded module outputs and provider files, removes every affected object, and rebuilds the entire affected suffix. Its new BinomLegendre object also matched the separate historical independent replay, which failed final reauthentication on the subsequent HalfBinomial update. The earlier window refresh and unchanged population-refresh source hashes and Pell recurrence source/object were checked separately.

The replay exited successfully with no source warnings; the checks report `propext`, `Classical.choice`, and `Quot.sound`. The [61-file author evidence manifest](adaptive-sandwich-postmerge2011-author-evidence/FILES.json) has SHA256 `11ee3298f405273a79c4460508e3dcf7916d37a659a07af2915a33ef4bb06589`. It preserves all rebuilt sources, full logs and timing records, driver, provider manifest, and inherited state records. The author provider is `/tmp/adaptive13-sandwich-postmerge-u6_gfzbc/lib`. Package and toolchain interiors remain inherited boundaries.

The independent replay has the same explicitly authenticated
historical-provider and package boundaries as the author replay.

After these replays, an upstream merge moved the rank-lower proof into
`ArithmeticHalfBinomial` and updated `ArithmeticAdaptivePopulation2011`.
These passes therefore cover the preceding source snapshot; the affected
suffix must be rebuilt again for the merged sources.

The subsequently checked AuxBind client is outside this replay. CellWindow and the adaptive machine-halting wrapper still require a current-source continuation. This result does not establish existence of a syntactic HA proof.
