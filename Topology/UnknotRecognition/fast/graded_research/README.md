# Quantum-ordered transfer validation and measurements

These maintained drivers use production `fastunknot`. They were adapted from
report 23 without changing the delivered archive. Run from `fast/`, or invoke
the scripts by absolute path from another working directory:

```bash
python -B graded_research/validate_transfer.py --output /tmp/graded-audit.json
python -B graded_research/benchmark_transfer.py --rounds 7 --output /tmp/graded-benchmark.json
python -B -m unittest discover -s tests -p 'test_graded_transfer*.py'
```

The audit checks all eight special contraction identities at each eager
transfer stage, raw homology across four scanners, and quantum-resolved ranks
across three tracking scanners. It uses 86 diagrams, each with three crossing
orders. The synthetic controls exercise nonzero residual maps, higher-order
corrections, quantum-band zeroes, partially completed sparse elimination,
capacity fallback and deadlines. The integration tests additionally compare
small random diagrams with the existing set-coefficient scanner and verify
safe public options, component coefficients and continued gluing.

The benchmark uses seven shuffled paired rounds, an unchanged standard A/A
control, fresh states, warm runs, and recorded batching. Complete raw scans
include reduction setup but exclude construction and crossing-order search;
recognition filters are bypassed. Synthetic measurements time the whole
reduction stage but exclude cloning. Cyclic GC is disabled only during timed
operations. Correctness checks run outside those intervals. Synthetic controls
are valid graded complexes with a nonzero minimal dotted differential; their
realization as knot prefixes is not asserted. Small timing differences need
to be compared with A/A noise.

Production APIs accept `reduction="graded"` or `"graded-adaptive"` in
`khovanov_rank` and `recognize`. Direct `GradedTransferScan` construction also
supports `certificates=True` for expensive full identity checking and
`max_transfer_objects=LIMIT` for sparse fallback above that threshold.
The adaptive class spends the usual sparse-update allowance before transfer;
its counters record actual switches. These policies do not provide a
competitive-time or global state-size guarantee. The default remains standard.

Current evidence is in `../../synthesis/data/graded-*` and
`../results/graded_transfer_20261008.json`. The
[maintained theory](../../synthesis/graded_transfer.tex) records all hypotheses,
operation bounds, measured regressions and the remaining asymptotic problem.
