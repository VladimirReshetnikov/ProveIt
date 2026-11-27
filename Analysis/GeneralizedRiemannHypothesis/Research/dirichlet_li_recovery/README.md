# Finite Li measurements and two further transfers

Research notes on Vladimir Reshetnikov's ProveIt project, 27 November 2026.

## Start with heat.pdf

The explicit result is Theorem 6.3, on page 10. At time one, measurements of
255 Li heat coefficients on any one residue class modulo 20 determine the
multiplicities of the Riemann zeta and Dirichlet beta functions in a product.
An affine trend may be added to the logarithms of the magnitudes. Uniform
errors strictly below 1/12 still permit at most one pair of integer
multiplicities. The count is sufficient. Optimality of 255 is open here.

Theorem 6.1 proves finite-block separation on every fixed arithmetic
progression for a finite catalogue of primitive characters, bounded complex
weights, and polynomial calibration of prescribed degree. The constants for
this general statement are qualitative. Theorem 6.3 supplies numerical
constants in a two-character case. Its proof uses six coarse intervals from
FLINT and LMFDB, with the total contribution of all remaining zeros bounded
analytically. The checker verifies the rational bounds given those published
zero intervals.

Sections 1–5 treat an independent inverse problem for arbitrary admissible
critical-line spectra with integer multiplicities. They give a basis for
all signed changes invisible to a single time slice, the least number of
altered atoms and its equality cases, the sharp universal central band
of radius sqrt(3)/2, and finiteness of every actual fiber. A spectrum with
an empty central band of that radius has no other admissible spectrum with
the same time slice.

## Companion notes

| File | Result |
| --- | --- |
| torsion.pdf | Exact valuation budget for blocking simultaneous nonvanishing at unit powers on a single primitive cyclotomic shell in any dimension. The optimal endpoint for the first two powers at positive half-integral budgets is determined for every odd prime. |
| grover.pdf | Classification of periodic quadratic Fourier blocks of Grover walks on finite abelian groups of odd prime-power exponent. The multiplicities of the additional fourth- and sixth-root modes on the standard tori have explicit polynomial growth. |

The torsion note answers part of the article's question “Several powers”.
For nonconstant covering densities with mixed conductors, the general
several-variable exact cost remains open here. The Grover note attributes
the earlier two-angle classification and gives its higher-dimensional
extension and counts.

## Sources and scope

The project was read at commit
`4ccd0fdeda0b1cc316d2dfdccfdbcfea9d4b77fb`. The main points of comparison
are the article files `sections/li.tex`, `sections/rec.tex`,
`sections/tors.tex`, `sections/cost.tex` and `sections/gra.tex`. The pinned
Lean entry point exports the critical-line theorem for primitive Dirichlet
L-functions. Section 6 of the main note uses this as an input. The circle
classification and both companion notes are unconditional. The papers
supply mathematical proofs. The accompanying programs check finite
examples and certificate inequalities. The upstream Lean project was
not rebuilt and the new theorems have not been formalized in Lean.

[Project at the analyzed commit](https://github.com/VladimirReshetnikov/ProveIt/tree/4ccd0fdeda0b1cc316d2dfdccfdbcfea9d4b77fb/Analysis/GeneralizedRiemannHypothesis)

[Vendored Lean theorem declarations](https://github.com/VladimirReshetnikov/ProveIt/blob/4ccd0fdeda0b1cc316d2dfdccfdbcfea9d4b77fb/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Main.lean)

The related incoming reports inspected cover Dirichlet spectral
conditioning, inverse problems for Hermitian matrix couplings, moving
zero windows, two-frequency cancellation, fixed-cardinality torsion
estimates, prime character codes, sparse recovery from primes, character
fingerprints, growing factorizations, and five- and seven-step graph towers.
The proposed additions are relative to the pinned project and the
literature cited in the notes. Bibliographic priority remains open.

## Reproduction

Each PDF can be rebuilt with two passes of pdfLaTeX on its main source.
Keep the two input files beside heat.tex. The Python checks use the
standard library. Run the following commands from the extracted directory.

```sh
pdflatex heat.tex
pdflatex heat.tex
pdflatex torsion.tex
pdflatex torsion.tex
pdflatex grover.tex
pdflatex grover.tex

python3 check_window.py
python3 check_heat.py
python3 check_torsion.py
python3 check_grover.py
```

The checks respectively certify the explicit constants, compare the
circle classification with exact cyclotomic Fourier computations, verify
finite power covers and mixed-shell orbit sizes, and count Grover blocks
using cyclotomic arithmetic. The outputs from the delivered versions
are in checks/. SHA256SUMS covers every other file in the archive.
