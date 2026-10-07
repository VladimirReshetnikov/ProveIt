# Opt-in integration

1. Add this research package without replacing the default scanner.
2. Make `src/` importable (for example through `PYTHONPATH`).
3. Run `check_checkout.py --fast-dir ...` against the real checkout, then all existing tests.
4. Create a fresh `FastScan` and call `install_on_empty_scan(scan)` before any crossing.
5. Record `scan.algebra.kernel_stats` alongside existing scanner statistics.

The exact current interface audited is `Planar.compose(a, b, c, f, g)`. Its plan is either `None` or `(components, monomial_memo)`, and each component has five fields. The adapter uses the engine's own matching IDs and circle order, retains original topology compilation and crossing transfers, and clears its added component cache per stage.

Do not copy packed coefficients between `BitAlgebra` and `Planar` without an explicit basis conversion. Do not apply the scalar involution shortcut to matrix blocks. Do not use a same-ring tensor interface for heterogeneous matching types without a typed composition extension.

The block/tensor implementation is not wired into the scanner's object cancellation loop. Such wiring needs extraction of structured factors, basis-change/provenance certificates, grading/type handling, and bounds on representation growth. The JSON verifier certifies an algebraic Schur identity only.

Acceptance for a default switch requires a workload with genuinely dense calls, a non-regressive selector on ordinary inputs, complete-checkout correctness checks, and measurements on the deployment platform. The included ordinary scans do not establish this case.
