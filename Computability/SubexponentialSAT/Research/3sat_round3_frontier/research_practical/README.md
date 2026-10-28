# Practical exact packet extraction: paired grids and projective cubic filters

## Result first

Two exact, polynomial-space local alternatives improve the packet-entry operation
retained by the supplied proposals. Neither improves the global SAT exponent.

1. A classical centered/polarization (grouped Glynn) identity evaluates exactly
   floor(G/2) points instead of the forward difference grid's G. Guard precision
   is p+R−1+v2(product beta_j!), not p. Gray traversal updates row sums in O(R)
   rather than O(Rt) operations per point.
2. For positive target exponents all equal to 2, a projective cube-root filter
   evaluates G/3 points in the same ring and at precision p, with no factorial
   division. The source's degree-4*ceil(log2(s)) unramified extension already
   supports a primitive cube root. Mixed exponents in {1,2} are also supported,
   but the cube grid is selected only when its proven count is smaller.

Synthetic same-operation benchmarks show half-grid speedups 1.56–2.30x versus
an already Gray-optimized full forward grid on nine fixtures. Four all-two,
same-ring cube fixtures improve 2.71–3.00x over forward Gray, and 1.47–1.67x over
half-grid. Root materialization is explicit; additional timings pay Hensel lift
on each extraction. These are NOT full SAT or tensor-contraction benchmarks.

The mathematical derivation, integration contract, benchmarks, and limitations
are report-ready in `practical_exact_extraction.tex`.

## Files and reproducibility

- `packet_extraction.py`: independently written stdlib-only kernels, free-ring
  arithmetic, Gray enumeration, affine homogenization, Hensel lift, adaptive
  dispatch. No imported program is executed.
- `test_packet_extraction.py`: direct coefficient-multiplication oracle and
  normal/-O tests, including precision/canonical-lift negative controls.
- `tests.json`, `tests_optimized.json`: full test records.
- `benchmark_packet_extraction.py`, `benchmarks.json`: nine synthetic profiles;
  reference, strong forward-Gray baseline, and half-grid comparisons.
- `benchmark_root_filter.py`, `root_benchmarks.json`: four all-two profiles in
  identical extension rings; cached root and per-call Hensel lifting timings.
- `benchmark_dispatch_negative.py`, `dispatch_negative.json`: adverse all-one
  cubic filter case (19.1x slower); adaptive selection correctly avoids it.
- `sources.json`: primary external references for classical related methods.
- `optional_hybrid_filter.md`: a proved mixed ±1/cube-root improvement not yet
  implemented or benchmarked; intentionally excluded from measured claims.

Commands (from this directory):

```sh
python test_packet_extraction.py
python -O test_packet_extraction.py
python benchmark_packet_extraction.py
python benchmark_root_filter.py
python benchmark_dispatch_negative.py
```

## Trust and fairness

No imported source scripts, proof builds, installers, or upstream mutations were
used. Direct coefficient tables are verifier-only, never the production kernel.
Baseline and candidate operate on exactly the same polynomial, coefficient ring,
precision and canonical input representatives. The baseline is already Gray
optimized, but is not claimed globally optimal. It could skip the known zero
origin point, a one-evaluation improvement not material to displayed ratios.

The formulas are classical adaptations, not claimed as newly discovered general
permanent algorithms. Polynomial-space source integration is specified but no
full SAT executable has been built. All timings are shared-executor medians of
three calls after warmup, not isolated measurements or statistical significance.
