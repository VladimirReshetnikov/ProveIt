# Differential Equations over the Surcomplex Numbers

**Finite-phase obstructions for surreal derivations and support-controlled Hahn-coherent dynamics**

Prepared for Vladimir Reshetnikov, September 21, 2026.

## Deliverables

- `article.pdf`: the 27-page typeset article (cover, two-page contents, and 24 numbered pages).
- `article.tex`: complete standalone LaTeX source with an embedded bibliography; no external graphics or bibliography database.
- `REPOSITORY_AUDIT.md`: the precise documentation gap, inspected sources, pinned revision, and audit limitations.
- `verify_examples.py`: finite exact symbolic checks for the worked examples.
- `verification_report.json`: recorded successful run, 115 checks passed.
- `requirements.txt`: the SymPy version used for the checks.
- `build.sh`: a minimal LaTeX build command with error handling.
- `BUILD_REPORT.json`: build and inspection metadata.

## Scope

The repository already distinguishes coordinate, formal-parameter, and scalar surreal differentiation. This article develops the differential-equation theory left undeveloped in the inspected passages, rather than claiming those distinctions were absent.

For the normalized Berarducci–Mantova derivation, it proves that the equation

    partial y = (a + i b) y

has a nonzero surcomplex solution exactly when `b` has a finite surreal antiderivative. It develops an explicit obstruction, power and iterated-logarithm thresholds, the harmonic-oscillator obstruction, set-sized differential workspaces, and exact Laurent resolvents.

For coordinate differentiation, it proves common-domain Hahn-coherent existence, uniqueness, support bounds, variation of constants, determinant identities, monodromy, and a polynomially nonlinear perturbation theorem. Worked examples include noncommuting two-scale matrices, factorial Laurent solutions, a coherent entire Riccati solution with an infinite pole, and nontrivial infinitesimal monodromy. An appendix proves the support lemma.

The results are proved from explicitly stated hypotheses and attributed input theorems. No priority claim, resolution of a named published open problem, or machine-checked formalization is asserted.

## Build the PDF

From this directory, with a LaTeX installation providing latexmk, pdfLaTeX, Latin Modern, and the packages named in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

On a POSIX shell, `sh build.sh` performs the same operation. No network access is required to compile once the LaTeX packages are installed. The delivered build has no LaTeX errors, warnings, undefined references, overfull boxes, or underfull boxes.

## Reproduce the example checks

With Python and SymPy available:

```sh
python verify_examples.py
```

The delivered run used Python 3.13.5 and SymPy 1.14.0. The program writes `verification_report.json` next to itself and exits with an assertion failure if a check fails. The optional dependency file records the tested SymPy version:

```sh
python -m pip install -r requirements.txt
```

There are 115 exact checks. The matrix cutoff is total degree 6, not a valuation cutoff; the Laurent reciprocal-series order is 12. These are finite identity and residual checks, not proofs of arbitrary Hahn summability, scalar nonexistence, transfinite recursion, or the Berarducci–Mantova construction.

## Repository snapshot

The targeted audit concerns `VladimirReshetnikov/Surreal` at revision:

    e260237db9b71da8b74a0c13c8e6355119091100

No repository files were changed. See `REPOSITORY_AUDIT.md` for the source paths and the exact scope of the review.
