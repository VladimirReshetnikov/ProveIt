# Validation record

## Mathematical status

The article contains full proofs of the stated new theorems. The main bridge
is: a uniform Fourier upper envelope, a matching logarithmic average lower
envelope, exact positive-orthant conjugacy, and compact-support Fourier
witnesses for derivative norms. The resonant case has an independent parity
factorization and is not obtained by extending the distinct-modulus theorem.

This is an unrefereed draft. Proofs were not checked in Lean, Rocq, or another
proof assistant, and no independent peer-review claim is made.

## Executed checks

The recorded `python code/verify.py` run completed successfully:

- 1,200 exact rational cases in dimensions one through six, seven assertions
  per case; the envelope integral is independently evaluated from line crossings.
- 100 exact signed-parity cases, two assertions per case.
- One exact worked-area check.
- Total: 8,601 exact assertions passed.
- Five logarithmic-box and eight ray-window cases, each with 96 samples,
  evaluated at 160 decimal digits.
- Largest evaluated analytic logarithmic product-tail bound:
  9.9981079e-91.
- Maximum signed-factorization discrepancy in computed logarithms:
  4.5721612e-101.

These finite tests are error detectors, not a proof of the general analytic
results. The numerical products have an analytic truncation estimate but no
interval enclosure of rounding error; their reported values are diagnostics.
See `data/verification_report.json` for machine-readable versions and counts.

## PDF validation

The final article was built with three serial successful `pdflatex` passes.
The final log contains no errors, unresolved citations/references, rerun
requests, overfull boxes, or underfull boxes. The PDF has 21 A4 pages and
extractable text. It was rendered for visual inspection, including the title,
contents, proof pages, envelope diagram, numerical table, and final references.
Font embedding and page-boundary checks were also performed. Intermediate
TeX files and render images are not included in the deliverable archive.
