# Adaptive clients after the rank-lower refactor

An author replay passed the 17-module affected suffix from the updated `ArithmeticHalfBinomial` through the adaptive population, actual-zero window, and six reverse-construction clients with their checks. The rebuilt source snapshots and inherited provider files matched again at completion. An independent replay at `/tmp/adaptive13-ranklower-postmerge-tjqelwlk` also passed, with all 17 source, object and complete-log hashes matching. Both are suffix replays over the independently accepted Sandwich provider, not fresh builds of the full transitive closure.

The upstream update moved the existing rank-lower proof into the new `ArithmeticHalfBinomial.rank_lower_of_radix` theorem and changed the adaptive population theorem to call it. The existing adaptive theorem statement is unchanged. The 14-variable HalfBinomial2011 wrapper also changed upstream, but it is outside this adaptive suffix. The replay excludes all 17 affected old objects, rechecks the unchanged population/window refresh and Pell recurrence source records, and rebuilds the affected modules in dependency order.

All modules exited successfully without source warnings; their checks report `propext`, `Classical.choice`, and `Quot.sound`. The [58-file author evidence manifest](adaptive-ranklower-postmerge2011-author-evidence/FILES.json) has SHA256 `2fd39a6081dcfc931cbe2bc7464909e2b2d8f46024c6258823d57ae230b2a802`. It preserves all rebuilt sources, complete logs and timing records, driver, provider manifest, and earlier state records. The author provider is `/tmp/adaptive13-ranklower-postmerge-tdfnxwn4/lib`; package and toolchain interiors remain inherited boundaries.

AuxBind and the machine-halting/CellWindow closure require separate source-current replays. This result does not establish existence of a syntactic HA proof.

A later upstream merge again changed HalfBinomial and AdaptivePopulation2011.
This packet covers the preceding source snapshot; the affected adaptive and
assembly descendants require rebuilding against the merged sources.
