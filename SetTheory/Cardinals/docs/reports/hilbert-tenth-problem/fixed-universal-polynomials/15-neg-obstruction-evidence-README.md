# Raw29/positive21 negative-index obstruction

## Outcome

A full positivity theorem and a full negative compiler zero remain unresolved. This packet proves and independently audits an exact necessary-and-sufficient criterion for a negative zero, with every omitted outer, input, first/main Pell and ordinary auxiliary witness reconstructed positively.

The new parts are:

1. Deterministic packing recovery: after q and the main index p, Z and F are forced; the selected input index forces W. The remaining tests suffice for a full positive child zero, not only a subsystem.
2. A rationally certifiable narrow real window for p of length less than q^(-3)+q^(-5). It rejects or isolates a possible integer without constructing giant Pell values; final ratio acceptance still requires a rigorous comparison.
3. The wrapped odd-input branch is finite for each fixed compiler and input, with an explicit q,w bound. It is empty for x=1 or x=2. In the unwrapped branch W=2^u exactly.
4. The even-input branch satisfies the sharper coupled bound us<=C<=q-u+b-1, hence u(s+1)<=q+b-1.

The two-unbounded-parameter count, bounded first-index representatives, and at-most-one odd p were already available from prior reductions. They are credited accordingly. The all-odd-p auxiliary completion is also existing upstream work; the new result is using it to close all full-system sufficiency obligations.

## Files

- `EXACT-OBSTRUCTION.md`: complete proof and precise novelty/unresolved boundary
- `independent/INDEPENDENT-REVIEW.md`: separate mathematical/source audit
- `check_exact_obstruction.py`, `check_results.json`, `expected_check_results.json`: own exact mathematical checks and frozen receipt
- `release_hardening_results.json`, `guard_regression_results.json`: normal/optimized replay and unconditional-failure evidence
- `final_source_freshness.json`: final-freeze source identity check
- `independent/`: independently written checkers and receipts
- `source_manifest.json`, `sources/`: five authenticated, immutable upstream text/data snapshots
- `context/`: earlier reviewed reduction and audit, preserved as prior work
- `MANIFEST.sha256`: local packet checksums

## Checked scope

The own checker passes 18,360 packing fixtures, 288 input fixtures, 450 exact rational Binet comparisons, both auxiliary parity classes, and 16 large-index divisibility cases. Its exact outward-rational filter excludes all 3,536 parameter choices in the documented relaxed scale grid q in {16,20,32}, w=1..4, all bounded s,t. These are not claimed actual compiler instances. No full negative zero was materialized and no unbounded exclusion is inferred from the grid.

The three checkers are read-only by default and emit deterministic canonical JSON on stdout. Their `--expect` option compares a frozen receipt byte-for-byte; `--output` accepts an external destination outside the packet. All verification uses unconditional exception checks and remains active under `python3 -O`. Run the commands below from the packet directory, or supply the corresponding relative paths from another directory. The source schedules are read as data only and never executed. Only newly authored checking code runs. No repository clone, upstream modification, external artifact upload, or source schedule execution occurred.

    python3 check_exact_obstruction.py --expect expected_check_results.json
    python3 -O check_exact_obstruction.py --expect expected_check_results.json

    python3 independent/audit_exact_obstruction.py --expect independent/expected_audit_results.json
    python3 -O independent/audit_exact_obstruction.py --expect independent/expected_audit_results.json
    python3 independent/audit_log_windows.py --expect independent/expected_log_window_results.json
    python3 -O independent/audit_log_windows.py --expect independent/expected_log_window_results.json

The completed normal/optimized replay receipts are recorded at the packet root and under `independent/`. No checker overwrites frozen expected results by default. The packet can be copied intact and replayed without the original author workspace.

## Source pin

The read-only source snapshot is ProveIt commit d5bd4a67b41b89688a079997574a94bcd855bb83. The targeted refinement remains the version introduced by 813c1cff42f9238a0158228f5e003a6a5405444a. The nonlinear projected source bytes are unchanged from the previously independently reviewed receipt. Unrelated source claims about the newer universal 85-operation polynomial are not reviewed or promoted here.

At final freeze, all five relevant Git blobs were rechecked unchanged at main commit 0f7d618f43bcb6361cee432273ba644e7defd951 (2026-10-03 19:39 UTC). The original authenticated source snapshots remain unchanged; unrelated newer commits are not audited here.
