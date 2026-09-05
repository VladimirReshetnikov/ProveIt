# Rational Resonances and Coalescing Roots of the Thue–Morse Polynomials

**Exact moment calculus, Gaussian–Fabius limits, and cyclotomic transform quotients**

Research companion prepared for Vladimir Reshetnikov, 4 September 2026.

## Contents

- `thue_morse_rational_resonances.tex`: complete, self-contained LaTeX source, including bibliography.
- `thue_morse_rational_resonances.pdf`: compiled 30-page article.
- `verify.py`: commented exact-arithmetic and high-precision verification program.
- `requirements.txt`: tested Python dependency versions.
- `Makefile`: PDF build and verification commands.
- `results/verification.json`: complete machine-readable verification report.
- `results/modulo_three_moments.csv`: directly evaluated weighted residue sums.
- `results/finite_depth_errors.csv`: errors before and after cubic correction.
- `results/gaussian_limit_errors.csv`: Gaussian–Fabius double-scaling experiment.
- `results/hierarchy_errors.csv`: linear, quadratic, and cubic hierarchy experiments.
- `SOURCES.md`: primary-source comparison notes.

## Main results

Theorem 3.1 constructs entire rational-frequency profiles with an exact finite-depth tail identity. Theorem 3.3 gives a convergent correction expansion and an explicit analytic remainder bound. Theorem 5.1 gives every twisted power moment by a finite Bell polynomial; Theorem 5.2 derives explicit eventual recurrences for polynomially weighted arithmetic-progression sums.

Theorem 7.2 proves the coalescing-root hierarchy, including the Gaussian–Fabius limit in Corollary 7.3. Theorem 8.1 identifies a cyclotomic product of the odd-order profiles with an integer-dilation quotient of the Fabius transform. Theorem 9.1 proves a sharp singularity/differentiability classification for the resulting digit-series laws.

Theorem numbers are those of the supplied PDF. The mathematical proofs are in the article; the code is an independent consistency check.

## Reproduce the PDF

A reasonably current TeX Live or equivalent installation is needed, including `newtx`, `amsmath`, `amsthm`, `mathtools`, `microtype`, `geometry`, `booktabs`, `fancyhdr`, `xurl`, `hyperref`, and `latexmk`.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error thue_morse_rational_resonances.tex
```

Alternatively run `pdflatex` on the source repeatedly until cross-references and the contents are stable. There are no external images or bibliography files to obtain. No font files are included in the archive.

## Reproduce the computations

Python 3.10 or later:

```sh
python -m pip install -r requirements.txt
python verify.py --output results
```

The verification program uses ordinary assertions. Run it without Python's `-O` option. It checks 252 odd-order and 156 dyadic exact identities in cyclotomic quotient fields, plus the displayed residue examples. Every exact equality passed in the supplied run.

The numerical calculations use 65 decimal digits and up to 270 factors. The finite-depth and cyclotomic identities are checked to tight tolerances, and three double-scaling regimes are tabulated. These numerical evaluations are not interval-arithmetic certificates; the article's analytic bounds and proofs justify the theorems.

## Scope and novelty

The reference atlas and selected primary papers were consulted. Ordinary Prouhet cancellation, the classical binary product, the basic Fabius bridge, general automatic-sequence recurrence mechanisms, and uniform-convolution splines are treated as background, not claimed as discoveries.

The coalescing-root hierarchy and the combined profile–moment–quotient development are proposed extensions not identified in the inspected sources. This is not an exhaustive historical-priority claim, peer review, or Lean formalization. Individual complex profiles and finite renormalized approximants are not asserted to be positive probability transforms. The positive interpretation of the Gaussian member applies to its limit.
