# Optional symbolic and numerical audits

These programs preserve the original independent audit calculations, with small
portability changes: hardcoded workspace output paths were replaced by a required
new `--output-dir`, and mathematical `assert` statements were made explicit
runtime checks. No internal research notes, account identifiers or service
receipts are included.

Dependencies, not installed by this package:

- Symbolic `derive.py` programs: SymPy (recorded replay used 1.14.0)
- Numerical `check.py` and `exterior_check.py`: mpmath (recorded replay used 1.3.0)

The standard-library core, builder and guards do not import these packages.
Install optional dependencies only if you want to rerun these additional audits.
Run from the extracted package directory, directing results outside the package:

```
python -B optional/boundary/derive.py --order 4
python -B optional/boundary/derive.py --order 6
python -B optional/window/derive.py
python -B optional/boundary/check.py --output-dir ../boundary-diagnostics-new
python -B optional/window/check.py --output-dir ../window-diagnostics-new
python -B optional/window/exterior_check.py --output-dir ../exterior-diagnostics-new
```

Each numerical command requires that its output directory not already exist.
The symbolic commands print to stdout. The saved `coefficients.txt`,
`coefficients_order6.txt`, `diagnostics.json`, `exact_counts.json`,
`integer_checks.json` and `exterior_diagnostics.json` provide reference output.
Floating-point output may vary with software versions. Exact integer records
should agree independent of version.

The numerical programs sum positive terms about an integer mode, using monotone
ratios to estimate omitted tails at ordinary arbitrary precision. Their reported
tail bounds are not outward-rounded enclosures of all numerical error. The
exterior total-variation value also truncates a numerical sum, so it is a
convergence diagnostic rather than a certified total-variation enclosure. None
of these diagnostics is used as proof of the report's asymptotic remainder or
uniformity claims.
