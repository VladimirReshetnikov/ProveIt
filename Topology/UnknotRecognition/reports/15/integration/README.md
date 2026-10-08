# Opt-in integration

Suggested destination: `Topology/UnknotRecognition/research/radical_transfer/`.
No files in the upstream repository were modified. No full upstream tests were
run in this environment. The included braid harness and min-fill baseline are
not `fastunknot.scan_fast.FastScan`.

`profile_scancomplex.py` is a non-mutating adapter for the **reference**
`fastunknot.scan.ScanComplex` interface reviewed in this report, using bit
algebra. Instrument a stage just before its existing `eliminate()`:

```python
from profile_scancomplex import predict_scancomplex
prediction = predict_scancomplex(complex_)
complex_.eliminate()
assert len(complex_.objects) == prediction['minimal_survivors']
```

Measure the prediction separately. The input must already be a valid
differential: this lightweight adapter does not check its square.
A large prediction is a representation/resource warning, never a knot verdict.
Set-based morphisms are rejected. The optimized `FastScan` layout needs its own
adapter; this module does not guess that representation.

First deploy the oracle behind a diagnostic flag. Run all upstream Python/Rust
cross-checks before modifying defaults. Only then add block transfer, with
reviewed conversions of matching and circle bases and exact contraction checks
on small cases. Benchmark inputs that actually reach the Khovanov backend after
the current cheap filters, not just readily rejected nontrivial knots.

Do not carry profile counts between different scan prefixes. Do not discard the
radical differential after calculating the counts. Do not apply the scalar
self-inverse shortcut to block matrices. A budget refusal is never 'knotted'.
