# Exact Boundary Corrections for Thue–Morse Diffraction

**Signed Stern polynomials, positive spectral extrapolation, and sharp Sobolev limits**  
Research article prepared for Vladimir Reshetnikov, 4 September 2026.

## Read

Open `Thue_Morse_Boundary_Corrections.pdf` (25 pages). The main source is
`Thue_Morse_Boundary_Corrections.tex`; its bibliography is inline.

The article proves an exact signed-Stern boundary formula for finite Thue–Morse
Fourier coefficients, a positive two-level correction that reproduces an entire
Fourier band, a universal distributional correction, an analytic defect
factorization with positive binary-partition coefficients, sharp Sobolev error
rates, and an amplitude-parameter extension with positivity threshold -2/3.

Classical autocorrelation recurrences, Stern polynomials, and the square-moment
exponent are acknowledged as existing mathematics. The proposed novelty is the
finite-size synthesis and its consequences; a literature search does not certify
worldwide priority. No new Lean formalization is claimed.

## Exact verification

Python 3.9 or later, standard library only:

```sh
python verify.py --output verification.json
```

The included report records **19,037 passing exact checks**. The checks use
integers and `fractions.Fraction`, including independent Laurent-polynomial
multiplication, direct finite correlations, and power-series coefficient
identities. Direct correlation levels are 0 through 10, and the parameter tests
use nine nonzero rational amplitudes at levels 0 through 7. These finite tests
are supplementary to the mathematical proofs, not proofs of infinite limits.

The report's decimal exponents are descriptive floating-point values; they are
not used to decide the exact tests.

## Build the article

With TeX Live or another installation providing the packages in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error Thue_Morse_Boundary_Corrections.tex
```

Without `latexmk`, run `pdflatex` on the main source three times. The source uses
Libertinus when available and otherwise Latin Modern. No font files are included.
The two figure PDFs and `poisson_table.tex` are already present, so the article
can be built without running the numerical scripts.

## Regenerate figures and numerical table

Optional dependencies:

```sh
python -m pip install numpy matplotlib mpmath
python make_figures.py
```

The Poisson example uses 160-digit arithmetic and an independent 2,201-term
limiting-series evaluation. Its rounded numbers are illustrations, not certified
interval computations. The signs, bracketing, and convergence statements are
proved in the article. Numerical data are saved in `poisson_data.json`.

## File contents

- `Thue_Morse_Boundary_Corrections.pdf`: compiled article.
- `Thue_Morse_Boundary_Corrections.tex`: main source with inline references.
- `poisson_table.tex`: generated table included by the main source.
- `verify.py`, `verification.json`: exact tests and their recorded results.
- `make_figures.py`, `poisson_data.json`: optional numerical reproduction.
- `figures/`: the two figures in vector PDF and PNG formats.
- `PROVENANCE.md`: source and literature audit.
- `SHA256SUMS.txt`: checksums for the other delivered files.

The archive does not contain the supplied atlas, third-party paper PDFs, TeX
build intermediates, font files, or an unverified Lean implementation.
