# Derivations, Differential Equations, and the Phase Obstruction
## Over Surreal and Surcomplex Numbers

A 27-page standalone article prepared for the Surreal documentation project,
21 September 2026.

## The documentation gap

The inspected repository distinguishes function derivatives from scalar-field
derivations, and its trigonometry documentation explicitly does not choose
an intrinsic derivation or classify differential-equation solutions. This
article develops that bridge for the normalized Berarducci–Mantova derivation
D(omega) = 1. See `source_audit.md` for the pinned revision and audit scope.

## Main content

- An exact phase criterion for nonzero solutions of D(y) = (a + i b)y in
  No[i]: a real primitive of b must be finite.
- The logarithmic-derivative image and its purely infinite obstruction;
  the maximal domain No + i O for an intrinsically compatible exponential.
- Normalized primitives, their integration-by-parts correction, and
  inhomogeneous equations with a valid integrating factor.
- A complete classification of homogeneous ordinary-constant-coefficient
  scalar equations and constant matrix systems over this differential field.
- Exact derivative and logarithmic-derivative images in C((t^Q)),
  t = omega^(-1), with workspace-versus-ambient solution tests.
- Derivation-stable set-sized Hahn localization, a strong Hahn evaluation
  chain rule, and the distinction between intrinsic and fine differentiation.
- The established restricted composition bridge for omega-series, and an
  explicit Picard–Vessiot extension that cannot embed differentially into No[i].

Deep structural inputs are attributed. The connecting deductions are proved
in the text. No novelty, priority, or formal-verification claim is made.

## Files

`article.tex` — self-contained LaTeX source, including the bibliography.
`article.pdf` — compiled 27-page article.
`verify_examples.py` — exact finite Hahn and symbolic verification program.
`verification.txt` — executed results: 291 checks passed, zero failures.
`requirements.txt` — tested Python dependency.
`source_audit.md` — repository and literature inspection boundary.
`build_record.txt` — compilation and visual-inspection record.

## Build the PDF

From this directory, with a standard TeX Live or MiKTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex` repeatedly until references settle. No external
images, BibTeX/Biber run, network access, or shell escape is required. The
source uses standard AMS packages, Latin Modern, mathrsfs, geometry,
microtype, booktabs, longtable, xcolor, enumitem, fancyhdr, needspace, xurl,
hyperref and bookmark.

## Reproduce the finite checks

Use Python 3.10 or later. The delivered execution used Python 3.13.5 and
SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

The checks validate finite exact examples, rational support shifts, and
finite formal coefficients. They do not implement the full Berarducci–Mantova
derivation, validate arbitrary infinite supports, or machine-check the article.

The finite classifier accepts exact Gaussian-rational coefficients and
rational exponents. A certificate `r, k` denotes the solution
`t^r * E(k)` with the support-certified infinitesimal exponential, not a
finite expansion of every term of that solution.

The GitHub repository was inspected read-only; it was not modified.
