# Graded transfer measurements

Run from the package root:

```bash
python benchmarks/graded_transfer/benchmark_transfer.py
```

The script resolves both the implementation and the synthetic controls relative
to its own path. It records seven randomized paired rounds and an identical
baseline A/A control. Small cases are batched; cyclic garbage collection is
disabled only during timed operations. Input preparation, validation, ordering,
and cloning are excluded. The ordinary diagram measurements are complete raw
scans, bypassing all recognition filters.

`paired_measurements.json` preserves the delivered run. A new run defaults to
`measurements_reproduced.json`. Exact rank and surviving-map checks remain active.
The dense two-term controls satisfy the grading equations and retain a nonzero
minimal differential `x`; they are not claimed classical-diagram prefixes.

Eager transfer slows the ordinary stress input in these measurements, while its
kernel gains grow on the dense controls. Ordinary adaptive control cases invoke
no transfer stages. Ratios are descriptive host measurements, and A/A variation
must be considered before interpreting small differences.
