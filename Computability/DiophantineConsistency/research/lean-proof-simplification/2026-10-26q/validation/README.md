# Exact validation scope

`replay-results.json` records all 13 successful checks using the final packaged sources.
The logs are named by the check identifiers. All target axiom reports contain only
standard Lean axioms, or an empty list for the two semantic cores.

Checked production-namespace modules: the new ConsecutivePellUnit, replacement
ConsecutivePell, and complete modified MinimumNorm. MinimumNorm was replayed
independently against freshly compiled original ConsecutivePell and ShortEquation.
The exact new ShortSystem obstruction proof was checked in its small adapter file.

Not checked as full modules: modified ObjectAdditionCancellation, ObjectNaturalZero,
InternalSat, NaturalCases, NativePellBootstrap, and ShortSystem. No full project
build or production endpoint comparison was performed. The generic certificate
closure adapter to ObjectCodeBound remains a design proposal.

Both internal patch alternatives and the Pell/minima combined patches passed
textual `git apply --check`. See their per-topic receipts for exact measurements.
`pdf-qa.json` records final PDF checks; `pdf-build.log` is the successful final build.
