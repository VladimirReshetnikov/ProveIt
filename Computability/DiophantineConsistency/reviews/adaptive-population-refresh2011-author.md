# Adaptive population prerequisite refresh: author result

The author rebuilt eight current sources in dependency order against the
adaptive transport-restoration provider:
`ArithmeticPow`, `ArithmeticHalfBinomialSandwich`, `ArithmeticBinomPascal`,
`ArithmeticBinomExpansion`, `ArithmeticBinomFactorial`,
`ArithmeticBinaryPopulation`, `ArithmeticBinomLegendre`, and
`ArithmeticHalfBinomial`.

The previously audited binomial overlay `/tmp/outer-seed-bound-sharing/common`
was used only as a fallback for Foundation objects, including HFS Vec. All
380 shared Foundation artifacts were byte-identical to the adaptive provider;
no old project or BusyBeaver objects were taken from that fallback. The
fallback's prior independent review is included in the evidence, while the
Foundation/package/toolchain interiors remain inherited cached boundaries.

Both fresh author runs passed with identical source, object and complete-log
hashes for all eight modules. Both record one existing linter warning in
`ArithmeticBinomLegendre.lean:80` suggesting `simp` instead of `simpa`; it was
not suppressed or edited. This refresh requires independent replay. First
provider `/tmp/adaptive13-population-refresh-_07ro6yf/lib`.

The [55-file evidence manifest](adaptive-population-refresh2011-build-evidence/FILES.json)
SHA256 is `4f4c9ae9e8d4fa1cd9e6f98dcc0801dadf118367b4e1368f7c42a2ac7a1d929a`.
It contains both source snapshots, provider inventories, drivers, logs,
timings, states and the prior fallback review.
