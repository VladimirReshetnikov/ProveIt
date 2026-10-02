# A122399 research package

This package proves and extends the previously posted leading asymptotic for OEIS A122399. The polished eight-page mathematical report is `a122399-report.pdf`, with editable source `a122399-report.tex`. The pre-layout mathematical source is `proof.md`.

Contents:
- Exact vertical contour, nonasymptotic exponential truncation bound, and branch-safe strip decomposition
- Compact-direction two-size all-orders theorem and explicit finite coefficient formula
- Exact rational correction expressions and diagonal coefficients through order seven
- Controlled real inverse and asymptotic integer-threshold ceiling envelopes
- Block-count Gaussian limit, linear variance, and constant mean correction
- Elementary proof of the posted mod-prime periodicity conjecture, with a prime-power extension

The existing leading equivalent is credited to Vaclav Kotesovec's OEIS entry. Standard saddle/ACSV methodology is credited, including the nearby Khera–Lundberg–Melczer paper. No global novelty claim, least-period claim, or canonical transseries-sector expansion is made.

## Reproduce

Python 3.12 with mpmath 1.3.0 and sympy 1.14.0 was used. PDF assembly also uses Pandoc and pdfLaTeX with standard TeX Live packages. From this directory, run `bash verify_all.sh` for the complete producer, PDF, and independent-audit replay. Individual mathematical checks are:

```
python check_a122399.py > test_output.txt
python export_exact_coefficients.py
python verify_contour_inverse.py > contour_inverse_output.txt
python verify_congruences.py
```

The main coefficient generator uses exact symbolic rationals and asserts the absence of symbolic Float atoms. Numerical arithmetic uses 90 decimal digits. Its coefficients are derived from phase Taylor coefficients, not fitted to observed sequence values. Integer values use an independent recurrence for k! S(n,k).

The scripts verify exact sequence values and scaled remainder behavior through n=800, moments, nine finite-contour/tail bounds including off-diagonal cases, 40 inverse cases at five truncation orders, and 1621 congruences in 23 prime-power cases. These finite checks do not replace the analytic proofs or make implicit asymptotic constants into certified finite-n constants.

Independent audit materials are under `audit/`. The audit uses direct composition and a distinct Lagrange saddle-coordinate method, not the producer coefficient generator. Both producer and independent reviewer inspected all eight rendered pages. No clipping, overlap, missing glyphs, or TeX layout warnings remain. `make_report.py` deterministically assembles the TeX; `build.sh` produces a date-free, reproducible PDF. `SHA256SUMS` records release files. Rendered PNGs and TeX build intermediates are deliberately excluded from the release ZIP. The proof's Section 2 tail bound is explicit; the all-orders and inverse O-constants are asymptotic existence constants.

Working decimal values preceding the exact-rational contamination check were superseded. Only current generated outputs are authoritative. No remote upload, repository change, or OEIS submission was made.
