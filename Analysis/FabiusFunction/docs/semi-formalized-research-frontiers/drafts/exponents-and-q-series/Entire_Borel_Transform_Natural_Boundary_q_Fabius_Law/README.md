# An Entire Borel Transform at a Natural Boundary

**Sharp logarithmic Gevrey asymptotics for a dilation-normalized q-Fabius law**

Research article prepared for Vladimir Reshetnikov, September 30, 2026.
Developed with ChatGPT. The PDF has 23 physical pages.

## Main results

For independent uniform digits U_j on [-1/2, 1/2], the article studies

    F_z(t) = log E exp(z t sum_{j>=0} exp(-j t) U_j),    z real and nonzero.

It proves a complete leading equivalent for the odd asymptotic coefficients,
with a Lambert-W saddle and Gaussian prefactor. Their sharp refined type is

    lim (over odd j) log(j) (|b_j(z)| / j!)^(1/j) = 1/(2 pi).

The formal series is divergent, Gevrey one of zero exponential type, and not
Gevrey of any smaller nonnegative order. Its Borel minor is entire, admits an
exact positive-real-ray Laplace reconstruction, and has an explicit leading
double-exponential equivalent on the imaginary Borel axis. Nevertheless F_z
has a meromorphic natural-boundary interval on the imaginary t-axis. Thus its
entire Borel minor has no uniform exponential bound in any open angular sector
about the positive direction.

A companion frozen-amplitude theorem computes the complete meromorphic Borel
pole set, residues (including collisions), and exact factorial type.

## Scope

The transform is centered and dilation-normalized: its individual digit
amplitude is z t. This is related to the repository's original normalization
by the exact change of variables in equation (2.3); it is not asserted that
every sharp estimate transfers unchanged to a fixed original transform
argument. The separate minimal rational-moment denominator conjecture remains
open in this work. Worldwide publication priority has not been independently
established. No Lean or Rocq compilation was performed.

The theorems have conventional proofs. Exact and numerical tests are included
as supplementary evidence, not as substitutes for those proofs.

## Files

- `q_fabius_borel.tex`: self-contained LaTeX article with embedded bibliography.
- `q_fabius_borel.pdf`: compiled 23-page article.
- `verify_results.py`: reproducible exact and high-precision checks.
- `verification_results.json`: machine-readable receipt from the successful run.
- `verification_run.txt`: text transcript of that run.
- `CLAIM_LEDGER.md`: theorem-level scope and proof status.
- `SOURCE_NOTES.md`: repository pin and source-comparison limitations.
- `build_receipt.json`: PDF compilation and layout checks.
- `requirements.txt`, `Makefile`: dependency and build commands.
- `SHA256SUMS.txt`: hashes of the other distributed files.

## Build

Use a standard TeX Live installation with the packages named in the source.
No external bibliography processor, figure, or separately distributed font is
required. Run `make pdf`, or run the following command three times:

    pdflatex -interaction=nonstopmode -halt-on-error q_fabius_borel.tex

Three passes are used to stabilize the contents and cross-references.

## Verification

Python 3.10 or later is suitable. The recorded run used Python 3.13.5,
mpmath 1.3.0, and SymPy 1.14.0, with 75 decimal digits.

    python -m pip install -r requirements.txt
    python verify_results.py

To keep the distributed receipts unchanged:

    python verify_results.py --output-dir rerun_results

The script verifies 60 polynomial coefficient identities (495 nonzero
monomial coefficients), 90 numerical zeta/Bernoulli specializations, six
Laplace quadratures, independent imaginary-Borel evaluations, coefficient
asymptotic ratios, and selected boundary-cusp examples. Numerical calculations
are not interval-certified enclosures. The script needs no network once its
Python dependencies are installed.
