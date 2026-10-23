# Eleven-positive denominator-Y absorption

Canonical equation: `full_product.json`, eleven strictly positive integer
variables, exact total degree 958, 117 charged binary arithmetic operations.
The short-carrier alternative `short_product.json` has degree 962 and 115
operations. Both improve the pinned source38 eleven-positive frontiers in
degree and total operations. No global minimum or unrestricted-integer
eleven-variable theorem is claimed.

| Presentation | Residual degrees | Operations | Multiplications | Additions/subtractions |
|---|---|---:|---:|---:|
| Full product | 958 | 117 | 68 | 49 |
| Full system | 2, 956 | 113 | 67 | 46 |
| Full shifted system | 2, 956 | 112 | 67 | 45 |
| Full sum of squares | 1912 | 118 | 69 | 49 |
| Short product | 962 | 115 | 67 | 48 |
| Short system | 2, 960 | 111 | 66 | 45 |
| Short shifted system | 2, 960 | 110 | 66 | 44 |
| Short sum of squares | 1920 | 116 | 68 | 48 |

All additions, subtractions and multiplications, including scalar
multiplications, are charged. Fixed leaves and reuse are free; system
comparisons are free. Every supplied variable, fixed port and emitted gate
is live. Systems have two equations, not one equation per abbreviation.

## Files

- `PROOF.md`: full soundness/completeness and exact-degree argument.
- `section.tex`: integration-ready mathematical section.
- `report.tex`, `report.pdf`: standalone presentation.
- `full_product.json`, `short_product.json`: canonical single equations.
- `*_system.json`, `*_shifted_system.json`, `*_sos.json`: explicit alternatives.
- `build_eleven.py`: standard-library circuit emitter, payload and liveness checks.
- `check_eleven.py`: exact conjugate products, modular products, leading forms,
  full polynomial rays and pre-index bound diagnostics; requires NumPy.
- `BUILD_RECEIPT.json`, `CHECK_RESULTS.json`: reproducible primary results.
- `COEFFICIENT_BINDING.json`, `coefficients/`: one complete fixed coefficient tuple.
- `SOURCE_PINS.json`, `DEPENDENCIES.md`, `upstream/`: immutable sources and the
  precise inherited mathematical boundary.
- Sibling `elimination/INDEPENDENT_REVIEW.md`, `audit_eleven.py`,
  `audit_package.py` and result JSONs: independent AI-assisted review and audits.

## Reproduction

From the containing release directory:

    python batching/build_eleven.py
    python batching/check_eleven.py
    python -O batching/check_eleven.py
    python elimination/audit_eleven.py
    python -O elimination/audit_eleven.py
    python elimination/audit_package.py
    python -O elimination/audit_package.py

The two independent audits do not import batching or upstream code. They
parse JSON as inert arithmetic records. To rebuild the PDF, run pdfLaTeX
twice on `report.tex` from this directory. No network access is needed for
reproduction of the active circuits and diagnostics.

The whole-tuple adapter is included, but the compiler and blank-K215
syntactic-refutation calibration remain inherited theorems. The conclusion
is an ordinary mathematical equivalence formalizable in ZFC, not an
end-to-end proof-assistant certificate or proof of Con(ZFC).
