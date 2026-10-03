# Reproducibility and presentation verification

Date: October 2, 2026

## Mathematical and source review

The complete article source received a fresh independent PASS for the stated mathematics and bounded historical framing. The separate `review.md` records the reviewed source SHA-256 and the scope of that assessment. All sector and PGF coefficients through order six were independently reproduced. This is not formal proof-assistant verification or a worldwide-priority certificate.

## Clean extracted replay

The ZIP was inspected for unique safe relative paths, one top-level directory, no symlinks, and exact agreement with its embedded manifest. It was extracted into a fresh directory using `python3 -m zipfile -e`. The mathematical replay was then invoked as `bash replay.sh`; no executable-file permission was assumed.

The replay completed successfully using Python 3.12, SymPy 1.14.0, and mpmath 1.3.0. All five computation scripts passed. The comparison covered all six result JSON files and 427 scalar checks. Exact symbolic and rational fields agreed exactly; numerical decimal fields passed the stated 1e-40 relative-or-absolute tolerance.

The reproduced tests include:

- Universal sector and PGF coefficients through order six
- 120 path-power frontier-versus-subset and complement-count cases
- 1,199 finite-graph factorial-moment and second-root-statistic cases
- 100 affine-statistic values in 20 fixed-range families
- Fixed-distance logarithmic coefficients and smooth/chord inverse tests
- Both Gaussian sectors for disjoint triangles at four graph orders

## TeX and PDF verification

The PDF was rebuilt successfully from the clean extracted package using `bash build_pdf.sh`. The rebuilt PDF has 13 pages and its extracted text agrees exactly with the distributed PDF. PDF byte identity across build timestamps or TeX installations is not required.

Every page of the distributed PDF was rendered and visually inspected. All 13 pages were checked for clipping, overlapping text, missing mathematical glyphs, unreadable equations, broken references, and page-number/header consistency. No defect was found. The final TeX log contains no overfull boxes or unresolved-reference warnings.

## Scope of the certificate

The manifest certifies the bytes in this distribution. Numerical checks support the formulas and implementation; the analytic proofs supply the uniform all-finite-orders assertions. No explicit finite-input asymptotic-error constants, growing-degree theorem, convergent series, or smooth total-variation expansion across parameter branch changes is certified.
