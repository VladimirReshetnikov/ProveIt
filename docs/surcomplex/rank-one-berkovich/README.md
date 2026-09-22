# From Surcomplex Hahn Fields to Berkovich Geometry

**Rank-one convergence, Tate algebras, analytic annuli, and an entire-function case study**

A 30-page, standalone research exposition prepared for Vladimir Reshetnikov, dated September 21, 2026.

## The documentation gap

The Surreal repository already contains a comparison with Berkovich geometry. This article develops that comparison into a working rank-one analytic theory and an explicit bridge to the repository's coefficient rings. It is not based on a claim that Berkovich geometry is absent.

The audit is pinned to commit `e260237db9b71da8b74a0c13c8e6355119091100`. See `REPOSITORY_AUDIT.md` for the inspection scope and paths.

## Main content

The article works primarily in the set-sized subfield `K = C((t^R))` of the surcomplex numbers, with `t^gamma = omega^(-gamma)` understood as Conway's monomial map and the real-valued norm `|a|_v = exp(-v(a))`.

It distinguishes intrinsic norm convergence, strong Hahn summability, and the full surreal fine topology; proves strict inclusions between Tate, polynomial-coefficient Hahn, common-domain, radius-free germ, formal-coefficient, and open-disk analytic rings; gives a constructive one-variable preparation theorem, principal-ideal and finite-quotient results, analytic root counts, and a valuation Rouche theorem; constructs the relevant Berkovich disk points and annulus retraction; and computes analytic primitives and residues, including the contrast between the contractible annulus spectrum and its nonzero analytic de Rham class.

The worked entire series `F(Z) = sum_{n>=0} t^(n^2) Z^n` is credited to the repository's existing example and the classical partial-theta family. Its full zero geometry, first root corrections, derivative valuations, entire product, coefficient identities, and exact truncation certificates are proved. The first correction of its m-th normalized root occurs at `t^(m(m+1))`.

## Files

- `article.tex`: complete LaTeX source, with internal bibliography and TikZ diagrams.
- `article.pdf`: compiled 30-page article.
- `verify_examples.py`: standard-library-only exact finite checks.
- `verification.json`: full run record, including computed root expansions and all 542 assertions.
- `verification-summary.txt`: concise execution output.
- `REPOSITORY_AUDIT.md`: pinned repository sources and the scope of the gap assessment.
- `BUILD_REPORT.md`: build and rendering checks.

## Build

A standard TeX installation with the packages listed in the preamble is sufficient. No external images, bibliography database, shell escape, repository checkout, or separately supplied font files are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

To run the finite checks with Python 3.10 or newer:

```sh
python verify_examples.py --output verification.json
```

The delivered run used Python 3.13.5 and passed **542/542** assertions with exact rational arithmetic. The program uses no network and no third-party Python packages.

## Status

This is an expository synthesis and mathematical continuation, not a priority claim or the claimed solution of a named published open problem. Standard imported inputs are cited, and direct deductions are proved. The finite checks do not constitute a proof-assistant verification of the general arguments. No repository file was modified.

A suggested repository destination is `docs/surcomplex/rank-one-berkovich/`.
