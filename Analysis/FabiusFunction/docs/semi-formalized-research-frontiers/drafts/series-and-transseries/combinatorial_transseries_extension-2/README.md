# Combinatorial Transseries and Their Inverses
## q-Products, Finite Fields, Theta Sectors, and Arithmetic Sheets

A standalone extension of Vladimir Reshetnikov's *Transseries and Inversion*,
prepared 4 September 2026. The PDF has 39 pages, including a contents section,
proofs, numerical tables, implementation appendices, and linked references.

## Contents of this archive

- `combinatorial_transseries_extension.pdf`: the complete article.
- `combinatorial_transseries_extension.tex`: self-contained XeLaTeX source.
- `verify.py`: exact-arithmetic and high-precision verification program.
- `verification_report.json`: results from the supplied program.
- `reference_implementation.wl`: the Wolfram Language code from Appendix A.
- `requirements.txt`: the Python dependency version used for verification.
- `SHA256SUMS.txt`: file checksums.

## Main results and coverage

The central theorem gives a convergent inverse transseries for a quadratic or
linear exponential phase with an analytic exponential tail. Every coefficient
has a finite, nonrecursive expression. A general analytic-phase version covers
logarithmic phases and Lambert W centers.

Applications include general linear, symplectic, and unitary group orders;
complete and partial flags; fixed-rank and scaled Gaussian binomial
coefficients; q-factorials on both sides of q = 1; binomial-version q-Catalan
and q-Fuss-Catalan numbers; and generalized Galois numbers. For all weak flags
of fixed length, an entire theta-tail generating function gives every
exponential correction, followed by convergent inverse expansions on explicit
residue-class sheets. Weighted flag sums are included.

Further sections treat inversion near finite limits, primitive necklaces and
irreducible polynomials on fixed-radical sheets, an exact two-candidate integer
threshold rule, all necklaces, and the singular simultaneous large-index,
q-to-1 transition with its dilogarithmic inverse phase and modular scale.

Continuous inverses always refer to the specified interpolation. Integer
thresholds are treated separately. The fixed-parameter product and theta
inverse expansions are proved convergent; the small-h expansion in the
q-to-1 section is instead a finite-order asymptotic expansion with a remainder.

## Build the PDF

Use a TeX distribution with XeLaTeX and the standard packages named in the
preamble. Run the following command until the references stabilize, normally
three times from a clean directory:

```sh
xelatex -interaction=nonstopmode -halt-on-error combinatorial_transseries_extension.tex
```

The bibliography is included in the source; no BibTeX run, external graphics,
or network access is required. The source selects Computer Modern Unicode
when available, with Latin Modern fallbacks. No font files are distributed.

## Reproduce the verification

The program supports Python 3.9 or later. The included report was generated
with Python 3.13.5 and mpmath 1.3.0.

```sh
python -m pip install -r requirements.txt
python verify.py --output verification_report.json
```

The program uses no network access. The supplied run passed **1,090 checks**.
Integer enumeration and threshold comparisons use exact integer or rational
arithmetic; analytic checks use 110 decimal digits. Tests include the finite
inverse formula against an independent coefficient recurrence through weight
eight, exact sequence identities, theta expansions, weighted theta sums,
endpoint inversion, and arithmetic inverse coefficients. The report also
reproduces the numerical inverse-error and double-scaling tables.

These computational checks accompany the proofs; they are not a substitute
for the analytic remainder estimates. The Wolfram Language implementation
is provided separately for convenient reuse; it was not executed in a Wolfram
kernel during preparation of this archive.

## Source relationship

The base article was inspected at:
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/Transseries_And_Inversion

Its main TeX blob identifier was:
`aec3c70d4793e286b462e7d8894dede7c754995e`.

The article's bibliography links the relevant OEIS entries, official Wolfram
Language documentation, DLMF identities, and the literature on generalized
Galois numbers. In particular, the q-Catalan section extends the asymptotic
recorded by Vladimir Reshetnikov in OEIS A015030 in 2021. No claim of priority
over the existing literature is made.
