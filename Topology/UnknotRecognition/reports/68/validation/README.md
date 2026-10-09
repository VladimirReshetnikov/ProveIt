# Validation of the delivered research package

All records refer to the delivered snapshot unless a historical measurement is explicitly identified. These checks support the written proofs and software contracts; they are not Lean formalizations or a proof of quasi-polynomial recognition.

| Record | Scope and outcome |
|---|---|
| `full_suite.json`, `full_tests.log` | All 1,289 tests passed, with no failures, errors, or skips, using the pinned optional research dependencies. The run took 145.695 seconds. |
| `retained_proof_replay.json` | Independent native replay passed: 16,807 scalar height assignments; 32 distinct positive corpus bundles; six obstruction moves; the disc-to-disc-plus-two-spheres example; and six matched boundary reference certificates. Final measured source identities and retained historical source identities were checked. |
| `peeled_monotonicity.json` | All 812,500 exact algebraic checks passed. The checker uses literal half-integer slices and direct corner minima rather than the jump formulas. The 52 formal-vertex partitions are algebraic configurations, not a claim that every partition is realized by an ambient triangulation. |
| `integration_check.json` | The 21-file additive patch passed `git apply --check --whitespace=error-all`, applied byte-for-byte as intended, and left all 566 pinned baseline files unchanged. |
| `reproduction_smoke.log`, `../reproduced/run_checks.json` | The default standalone runner passed with no optional packages. One optional Regina comparison was skipped as expected. The feature-test log and repeated native proof/audit records are retained under `reproduced/`. |
| `latex_build.log`, `pdf_review.json` | The 30-page article compiled successfully. The log contains no overfull or underfull box reports. Every rendered page was visually inspected; the cover, mathematical derivations, results tables, figure, final claim ledger, and references also received enlarged inspection. |

The full suite and the standard-library smoke test are separate runs with different dependency environments. The skipped optional comparison in the latter does not change the zero-skip outcome of the former.

Benchmark claims use the final paired records identified by `article/experiments.tex` and `SOURCE_AUDIT.md`. Validation elapsed times measure checking cost, not recognition performance. Older exploratory measurements are retained with their exact source lineage and are not presented as timings of later corrected sources.
