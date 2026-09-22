# Differential Equations over Surreal and Surcomplex Numbers

**Canonical Derivation, Finite-Phase Obstructions, and Support-Certified Initial-Value Problems**

A 26-page companion article prepared after a targeted coverage audit of
`VladimirReshetnikov/Surreal`, pinned to commit
`e260237db9b71da8b74a0c13c8e6355119091100`.

## The selected gap

The repository has substantial analytic, geometric, trigonometric, and
computational coverage. Its trigonometry documentation explicitly does not
choose a scalar derivation or classify differential-equation solutions. Its
foundations documentation separates scalar derivations, fine derivatives,
and coordinate derivatives. This article develops that interface rather than
repeating the existing contour or trigonometry theory.

The audit read the documentation catalogue; the analysis, trigonometry,
foundations, and computer-algebra READMEs; and lines 1–220 of the trigonometry
article, all at the pinned revision. It was not an exhaustive source-code or
proof audit of the entire repository, and no repository files were modified.

## Main mathematical developments

The scalar derivative is the distinguished Berarducci–Mantova derivation,
normalized by delta(omega) = 1. For A in No[i], the equation delta(y) = A*y
has a nonzero solution exactly when Im(A) has a finite real primitive.
The purely infinite part of that primitive completely classifies rank-one
gauge equivalence. Consequences include nonexistence of nonzero scalar
solutions to delta(y) = i*y and delta^2(y) + y = 0, and a complete
classification of homogeneous equations with ordinary complex constant
coefficients.

The article also constructs an explicit oscillatory differential extension
with unchanged constants, proves a resolvent formula in real-exponent Hahn
workspaces, and analyzes an exact factorial Hahn solution with exponentially
small full-field ambiguity. Separately, it proves a common-domain coherent
initial-value theorem for positive-support nonlinear perturbations, with a
support certificate and a coefficientwise linear recursion. Riccati and
singularly scaled examples show the precise boundaries.

These are mathematical deductions and an expository synthesis, not a claim
of priority or of solving a named published conjecture. Deep structural
inputs are attributed to the primary literature. No theorem has been
machine-formalized or independently peer-reviewed here.

## Files

- `article.tex`: standalone LaTeX source with embedded bibliography.
- `article.pdf`: compiled 26-page article, with linked contents and references.
- `code/verify_examples.py`: deterministic exact symbolic regression checks.
- `requirements.txt`: the SymPy release used for the checks.
- `data/verification.json`: actual check results and tested software versions.
- `data/build_report.json`: PDF build and rendering checks.

## Build

A standard TeX distribution with the packages in the preamble is sufficient.
No bibliography processor, external graphics, or shell escape is required.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Reproduce the finite checks

```sh
python -m pip install -r requirements.txt
python code/verify_examples.py
```

The delivered run passed **150 of 150 exact checks**, using Python 3.13.5 and
SymPy 1.14.0. Checks include rational monomial primitives, product rules,
truncated resolvent residuals, factorial residuals, Riccati coefficients,
constant-coefficient examples, the Cayley phase identity, and oscillator
identities in a separately adjoined differential extension.

These checks use finite symbolic expressions. They do not implement the
surreal numbers, prove general support summability, or machine-check the
article's proofs. A successful finite regression suite is not a formalization.

## Suggested repository location

`docs/surcomplex/differential-equations/`, with cross-links to analysis,
trigonometry, foundations, and computer algebra. This is a suggested location,
not a claim that a directory or implementation has already been added.
