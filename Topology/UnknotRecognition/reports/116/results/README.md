# Frozen executed evidence

- `unit_tests.txt`: final 50-method standalone test run.
- `audit_exhaustive.json` and `.log`: 31,581 executed matrix roles, 63,162 plans and 1,241 positive-pivot comparisons. Some matrix families overlap.
- `audit_randomized.json` and `.log`: weighted/restricted/relabeling/transport/forest/path roles. Counts are not all disjoint inputs.
- `audit_large.json` and `.log`: analytic cactus and symbolic-cycle checks.
- `binary_cycle_2pow1024.json`: actual full six-state power certificate for a cycle with half-length `2^1024`; contains no expanded matching.
- `benchmark_all.json` and `.log`: every raw paired timing, A/A control, ordering seed, environment and summary. All samples completed.
- `article_build.log`: final three-pass LaTeX build log.
- `article_validation.json`: PDF extraction/render and warning checks performed before packaging.

The matrix benchmark compares with the explicitly supplied exponential subset oracle, not with the maintained ordered-interface solver or a best-known cactus method. The transport comparison answers the same row-sum query with both methods and includes validation/construction/serialization. Symbolic timings include complete-table proof replay and serialization.

Audit and benchmark scripts overwrite their default files. Use a copy or a new `--output` path for reproduction. The large suite also creates its example proof file. No native source geometry or real knot timing is represented by these data.
