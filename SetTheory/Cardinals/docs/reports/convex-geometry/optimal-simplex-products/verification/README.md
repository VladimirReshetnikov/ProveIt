# Exact verification for optimal simplex products

Both programs use only the Python standard library. Run from the
`simplex_products` directory:

```sh
python verification/verify.py --limit 300 --output verification/results
python verification/independent_audit.py
```

`verify.py` evaluates the factorial formula for the simplex values. It checks
seven strict rational interval certificates, the prime-power forms printed in
the manuscript, the first two-factor comparisons, and an independent dynamic
program that permits every possible final part size through dimension 300.
It compares that dynamic program with both closed formulas and checks the
sharp-gap examples. The JSON certificate contains positive integer differences
for both endpoints of every strict rational enclosure.

`independent_audit.py` constructs the simplex values from their consecutive
ratios, keeps the two highest distinct exact values in every dimension through
260, and retains all associated dimension multisets. It verifies the exact
optimizer, uniqueness as a multiset, and the sharp isolation factor. Keeping
two values is sufficient: any discarded value has two distinct larger values
at the same smaller dimension, and multiplying all three by the same final
factor preserves their order.

The finite programs are cross-checks. The manuscript's concavity and deficit
arguments prove the optimization and isolation theorems for every dimension.
The decimal values printed by the independent audit are descriptive only.

## Files

- `results/exact_certificates.json`: seven rational enclosures with positive
  cross-multiplication margins.
- `results/initial_comparisons.json`: exact ratios comparing two balanced
  simplices with a simplex in dimensions 13 through 20.
- `results/optimal_products.csv`: the optimizer and exact ratio to the simplex
  in dimensions 1 through 300.
- `results/verification_report.json`: output from the main verifier.
- `results/independent_audit_report.json`: output from the separate audit.
- `source_provenance.json`: original repository source path and Git blob SHA.

No external package, network access, or floating-point optimization is needed.
