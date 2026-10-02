# Partition sums of acyclic orientations

This package accompanies **Full asymptotic expansions for partition sums of acyclic orientations**, dated 1 October 2026.

## Results

- Full prefactors and arbitrary finite orders for OEIS A372395 and A370613
- Explicit first and second relative corrections in powers of n^(-1/2)
- A uniform quadratic majorant that controls signed Gamma tails and removes large-part cutoffs at relative precision
- Controlled Lambert-W inverse expansions and integer-threshold envelopes
- A fixed positive chromatic-parameter extension, uniform on compact parameter sets
- Exact sequence values through n=300, with independent n=150 replay and initial OEIS comparisons

The logarithmic constants and exact Gamma representation are prior results of Zhiyang Sun, arXiv:2605.04006v1. The report credits those results explicitly. It proves all orders in the Poincare sense and does not claim to resolve exponentially small sectors or provide an exponentially complete transseries.

## Files

- `orientation-partition-asymptotics.pdf`: complete report
- `orientation-partition-asymptotics.tex`: editable source
- `build.sh`: build the PDF with pdfLaTeX
- `first_correction.py`: direct first-correction evaluation
- `generic_second_correction.py`: finite formal generator evaluated through second order, independently of the hand-expanded first-correction formula
- `exact_check.py`: exact positive Touchard polynomial computation using carry-free Kronecker encoding
- `validate_results.py`: checks both exact arrays, all 21 initial OEIS terms supplied per sequence, asymptotic residuals, and inverse residuals
- JSON files: exact arrays and numerical results
- `independent_audit/`: independent mathematical and computational review records
- `manifest.json`: SHA-256 integrity manifest

The report gives the finite algorithm for any desired asymptotic order. The supplied coefficient-generation executable has been tested through second order; it is not described as an optimized arbitrary-order implementation.

## Short replay

Use Python 3 with `mpmath` and `sympy` installed. From this directory run:

    bash replay.sh

This runs the following three commands, then checks agreement between the two first-correction calculations:

    python first_correction.py
    python generic_second_correction.py
    python validate_results.py

The two independently organized coefficient calculations must agree on

    a1 unrestricted = -0.30756533355163369663854197121934666309...
    a1 distinct     =  0.23095021320861498101957980466695660800...

The generic generator gives

    a2 unrestricted =  0.01872663225856492421076350893326907627...
    a2 distinct     = -0.00424706612039284283055321876544848693...

The validation script ends with `PASS: exact OEIS initials and independent overlap`.

For additional independent tests, run `python independent_audit/checks.py`. This uses ordinary coefficient arrays through n=40, direct graph orientations through n=6, and a separately organized automatic-differentiation quadrature. It does not import the main calculation scripts.

## Full exact replay

    python exact_check.py 150
    python exact_check.py 300
    python validate_results.py

The n=300 computation is materially slower than the short replay and can take several minutes. It uses exact integer arithmetic throughout the sequence calculation; `mpmath` is used only for the subsequent asymptotic comparisons.

## Build the report

    bash build.sh

A standard TeX Live installation with the usual AMS, geometry, booktabs and hyperref packages suffices. The script has an optional fallback for the environment in which the report was produced; outside that environment it uses the normal pdfLaTeX configuration.

## Interpretation of the inverse

The integer sequence has no automatic canonical analytic continuation. The report constructs an eventually increasing smooth interpolant with the full differentiated expansion and explains why the inverse expansion is independent of that choice to every algebraic order. A finite inverse approximation yields a threshold envelope; exact rounding requires separation from an integer boundary.

## Reproducibility scope

Numerical checks support the theorem but are not its proof. The exact arrays are independently reproduced on the full n<=150 overlap. The all-orders theorem is justified analytically by the cutoff, root, Euler-Maclaurin, Fourier and Gamma remainder estimates in the report. The review record specifies which source revision was checked. Conventional external peer review remains appropriate before publication.
