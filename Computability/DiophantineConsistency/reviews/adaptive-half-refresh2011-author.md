# Adaptive half-index prerequisite refresh: author result

The exact adaptive-index consumer requires the current generic half-index
implementation. The author refreshed the current sources in dependency order:
`ArithmeticPellCommonUnit`, `ArithmeticPellStrongDivisibility`,
`ArithmeticPellIntegralSolution`, `ArithmeticPellIndexDivisibility`,
`ArithmeticPellPeriodicity`, `ArithmeticModularCancellation`,
`ArithmeticPellResidueClasses`, and `ArithmeticPellHalfIndex`.

The adaptive comparison and auxiliary providers were combined with the older
independently reviewed half-index provider. All 847 non-conflicting overlap
artifacts matched. Five differing old objects (GcdNormalization, Recurrence,
Classification, KnownUnit, Congruences) were excluded in favor of the
adaptive providers, and the eight downstream modules were rebuilt. The old
plan's eleven changed source paths were recorded. The first refresh attempt
failed when the current ResidueClasses source introduced a dependency on
ModularCancellation that was absent from the old overlay; the successful
attempts explicitly rebuilt it.

Both full author builds passed with identical source, object and complete-log
hashes for all eight modules, and no warnings. The independently replayed
Pell-index ancestor, accepted adaptive sources, and old half-index provider
supply inherited provenance; their selected files were rehashed. Package and
toolchain interiors remain inherited boundaries. First successful provider:
`/tmp/adaptive13-half-refresh-xn8fdq39/lib`. The root agent also reports an
independent replay matching all eight objects and full logs.

The [76-file evidence manifest](adaptive-half-refresh2011-build-evidence/FILES.json)
SHA256 is `d86eb33ae624a096373f4b6e9671c8b8cd312455b94fd57ece7ae241e6b9b1b0`.
It preserves the failed attempt, both successful attempts, driver code, source
snapshots, state, provider inventories, logs and timings.
