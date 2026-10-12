# Rectangular Cancellation Without Search

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

The article proves an exact full-elimination criterion for unsigned positive singleton cancellation, constructs independent sparse certificates, characterizes optimal row deferral, and proves exact passive-count transport with polynomial bit growth. A geometric three-ball family shows that deferral number need not be small merely because the manifold is a ball.

## Read first

`article/positive_cancellation.pdf` is the compiled article. Its source is `article/positive_cancellation.tex`; the benchmark table and highlight macros are separate generated TeX inputs included here. `CLAIMS.md` distinguishes proved mathematics, tested matrix algorithms, proposed integration, and work not run.

**No general quasi-polynomial unknot-recognition bound is claimed.** No difficult-knot performance run, full native suite run, or real-checkout patch application was performed. The paired measurements concern matrix kernels. Incoming archive metadata was inspected, but the two relevant binary archive bodies were not decoded; priority and overlap should be reviewed on integration.

## Reproduce

Use Python 3.10 or newer; this package was tested with Python 3.13.5. No third-party Python packages are required.

```sh
python -m unittest discover -s tests -v
python scripts/audit.py
python scripts/benchmark.py
sh build.sh
```

The test suite has 34 methods. The exhaustive audit compares 31,907 matrices against independent pivot-search, permanent and stopping-set oracles. It also checks 1,020 individual invariant cases and 1,241 optimal-deferral instances. The exact-transport tests include 400 randomized oracle comparisons and a 4,096-bit output constructed without expanded words.

The benchmark writes every sample to `results/benchmarks.json`, a CSV summary, and regenerated TeX table/macros. Timing values are environment-dependent. Rebuild the article after rerunning the benchmark so its displayed measurements remain synchronized. The document build requires a LaTeX installation with pdfLaTeX and the packages named in the source; it does not download anything.

## Minimal use

```python
from cancellation import column_cancellation_plan, verify_peeling_certificate

A = {0: {0: 1, 2: 1}, 1: {1: 1, 2: 1}}
plan = column_cancellation_plan(A)
certificate = {
    "schema": "positive-column-peeling-v1",
    "cancellations": plan["cancellations"],
    "remaining_rows": plan["remaining_rows"],
}
assert verify_peeling_certificate(A, certificate, require_complete=True)
```

This proves a **matrix claim only**. Source-authenticated geometric attaching curves and cocores are required for a topological conclusion. An arbitrary group presentation or homology matrix is not an acceptable source.

`deferred_plan(A, k)` finds the minimum deferred set when its size is at most `k`. Deferred rows remain genuine rows/two-handles; they are not discarded. `transport_exact_counts` computes exact nonnegative passive counts along a private schedule on the active rows. Neither function exports ordered embedded boundary patterns.

## Contents

- `article/`: self-contained mathematical manuscript with local TeX table inputs and PDF.
- `cancellation/`: producer, independent verifier, optimal small-deferral search, and exact transport.
- `tests/`: unit, adversarial, transfer, and integration-helper checks.
- `scripts/`: independent exponential oracles, exhaustive audit and paired benchmark.
- `reference/`: explicitly labeled transcription of two pinned native planner functions, not a full checkout.
- `integration/`: hash-guarded applicator and an independent core-verifier fast path.
- `results/`: actual logs, audit counts, samples, and validation metadata.

The eleven proposed research directions are also in `RESEARCH_QUESTIONS.md`. `SOURCE_AUDIT.json` records the exact reviewed source blobs and the unresolved incoming-archive comparison.

See `INTEGRATION.md` before applying anything to ProveIt. The applicator is dry-run by default. Existing general positive-pivot replay remains available; callers using partial schedules must not be globally redirected to full-decision peeling.
