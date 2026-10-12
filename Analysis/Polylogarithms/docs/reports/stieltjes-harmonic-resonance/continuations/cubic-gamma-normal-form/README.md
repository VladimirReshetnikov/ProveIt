# A Cubic-Background Formula for Gamma Normal Forms

**Date:** 11 October 2026  
**Purpose:** an additive research continuation for VladimirReshetnikov/ProveIt.

## Main result

The article proves the complete all-weight projection of the inverse-Gamma
Bell hierarchy onto functional monomials in `u0,u1,u2,u3`. In particular,
it supplies a finite rational expression for every coefficient
`[u0^a u1^k u2^b u3^n] N_(a+2k+3b+4n)`, for every `n >= 2`, including
all mixed `u2` factors and the parity zeros. The `n=2, b>0` case answers
Question 1 in the inspected **Affine Gamma Polarization** continuation.

The proof is an all-index variational argument with explicit polynomial
identities. It does not extrapolate from the finite verification table.
A nonrecursive pure-`u2` density, all-order Stieltjes endpoint identities,
anchored primitives, weighted digamma/Stieltjes evaluations, and finite
polylogarithm sums are included. Normal-form endpoint polynomials are
retained explicitly or by an exact terminating algorithm.

The arbitrary-highest-derivative formula in Section 9.3 is **UNPROVED**.
Its exact finite tests are separated from the proved cubic theorem.
Historical priority beyond the inspected sources is not established, and
the incoming binary archives were not exhaustively audited.

## Reading and source files

- `article.pdf`: complete article.
- `article.tex`, `preamble.tex`, `references.tex`, `sections/`: modular source.
- `standalone.tex`: the same article in a single compilable TeX file.
- `CLAIM_STATUS.json`: theorem and conjecture status, with scope limitations.
- `integration/`: proposed placement, status update, and a local-notation fragment.
- `provenance/`: exact inspected source identifiers and retrieval scope.
- `verification/`: exact programs, recorded JSON/text results, and certificates.
- `SHA256SUMS`: checksums of the delivery files (excluding itself).

The reference paths in the article point into ProveIt; no external TeX
source or remote download is required to compile this delivery.

## Build

A standard TeX Live installation with `latexmk`, `pdflatex`, Latin Modern,
`amsmath`, `amsthm`, `mathtools`, `mathrsfs`, `microtype`, and `hyperref`
is sufficient.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
# Or, in a fresh directory containing only standalone.tex:
pdflatex -interaction=nonstopmode -halt-on-error standalone.tex
pdflatex -interaction=nonstopmode -halt-on-error standalone.tex
```

## Reproduce the checks

Python 3.10 or later is intended; the recorded run used Python 3.13.5.
Install the packages in `requirements.txt`, then run from the package root:

```sh
python -m pip install -r requirements.txt
python verification/verify_exact.py
python verification/verify_endpoints.py
python verification/verify_numeric.py
# This is explicitly an exploration of an UNPROVED conjecture:
python verification/exploratory_all_orders.py
```

The scripts resolve output paths relative to their own location. Successful
runs overwrite their local result/certificate files. They require no
network access. The numerical Stieltjes quadrature is the most expensive
step. Exact tests and the build can also be run with `make exact` and
`make pdf`.

### Recorded exact checks

There are 31 full normal-form decompositions through weight 30, 973 cubic
coefficient comparisons (including parity zeros), 575 quadratic and 256
affine coefficient comparisons, four generic symbolic density identities,
216 beta/double-sum comparisons, and 288 endpoint-zero assertions.
A second exact program verifies four spectral evaluations, four rational
coefficient families, twelve partial-fraction identities, and the printed
`H8` and `N11` against the independent certificates.

Separately, 438 nonzero higher-derivative coefficients through weight 24
agree with the universal conjecture. These do not prove that conjecture
and do not check every absent monomial outside the proved sectors.

### Recorded numerical diagnostics

Thirty checks pass. They use 50 decimal digits, except for the generalized
Stieltjes integral at 35 digits. The configured residual tolerances are
`1e-38` and `1e-28`. These are floating-point diagnostics, **not certified
interval enclosures**. No proof-assistant formalization is claimed.

## Integration cautions

Normal reduction must precede truncation. A projected normal polynomial
is not the full normal polynomial at higher weights. The endpoint primitive
cannot be discarded in a definite integral. Hurwitz residues at order one
must remain present during Laurent coefficient multiplication. The article
contains explicit counterexamples or normalization checks for these points.

The source README contained a duplicated paragraph; the proposed editorial
correction is recorded separately. No mathematical error is alleged in the
narrowly inspected predecessor core. No remote repository changes were made.
