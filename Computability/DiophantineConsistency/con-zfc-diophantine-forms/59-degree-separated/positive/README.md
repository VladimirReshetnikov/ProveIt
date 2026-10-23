# Degree-316 ordinary-strong merger

This new equation has **12 strictly positive unknowns, exact degree 316,
and 102 charged binary arithmetic operations**. The same-variable-count comparator
is source52's twelve-positive degree-897 equation in 108 operations.
The improvement is structural: retain f, eliminate ordinary i rather than
normalized f, recover a separated radical sum through rational Pell
saturation, and deflate a known denominator factor from the norm.

| Presentation | Exact residual degrees | Operations | Multiplications | Additions/subtractions |
|---|---:|---:|---:|---:|
| Product equation | 316 | 102 | 61 | 41 |
| Three-equation system | 2,26,288 | 95 | 59 | 36 |
| Shifted system | 2,26,288 | 94 | 59 | 35 |
| Sum of squares | 576 | 103 | 62 | 41 |

All scalar multiplications are charged. No named register introduces a
quantified variable. Every gate, variable, and coefficient port is live.
The entire coherent source31 121-by-8801 tuple is bound by hashes and supplied.

The exact existence equivalence is to a blank K215 halt, hence a syntactic
ZFC refutation, through the explicitly inherited ordinary compiler and
calibration theorems. Negating existence gives the Con(ZFC) equivalence.
This is not a proof of consistency, global optimality, or a new end-to-end
proof-assistant certificate. It is not an eleven-variable improvement.

## Files

- `report.tex`, `section.tex`, `report.pdf`: five-page mathematical report and integration section.
- `PROOF.md`: expanded ordered proof, including rational Pell saturation.
- `ordinary_merger_product.json`: canonical single equation.
- `ordinary_merger_{system,shifted_system,sos}.json`: alternatives.
- `build_ordinary_merger.py`: new circuit builder with payload and liveness audit.
- `check_ordinary_merger.py`: inert-circuit algebra, full polynomial rays, and bounds.
- `check_merger_independent.py`: independently authored symbolic identity and DAG audit.
- `INDEPENDENT_REVIEW.md`, `REVIEW_RECEIPT.json`: independent AI-assisted adversarial review.
- `COEFFICIENT_BINDING.json`, `coefficients/`: coherent literal fixed coefficients.
- `DEPENDENCIES.md`, `SOURCE_PINS.json`, `upstream/`: exact inherited boundaries and provenance.

## Replay

    python build_ordinary_merger.py
    python check_ordinary_merger.py
    python -O check_ordinary_merger.py
    python check_merger_independent.py
    python -O check_merger_independent.py

The primary checker uses NumPy; the independent symbolic audit uses SymPy.
Build the PDF by running pdfLaTeX twice on report.tex in this directory.
No received upstream program is executed or imported. The whole source
compiler remains an inherited mathematical dependency, not something proved
by random tests, polynomial rays, payload verification, or circuit replay.
