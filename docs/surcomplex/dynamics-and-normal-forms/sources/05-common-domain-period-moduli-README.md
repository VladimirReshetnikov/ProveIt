# Global Infinitesimal Surcomplex Dynamics

**Complete period invariants, difference equations, and moduli beyond every
power of one infinitesimal**

Research manuscript, 21 September 2026. The PDF has 28 pages.

## Contents

- `article.tex`: standalone LaTeX source, with an internal bibliography.
- `article.pdf`: compiled article, with linked contents and cross-references.
- `verify.py`: exact finite-jet verification program.
- `verification.txt`: the actual recorded output (245 passing assertions).
- `requirements.txt`: the Python dependency used for the checks.
- `build.sh`: PDF build command, with a pdflatex fallback.
- `build_validation.txt`: final compilation and layout checks.

## Main results

Theorem 7.2 classifies globally defined, near-identity Hahn-coherent maps with
fixed leading displacement `t^delta a(z)`, where `a` is nowhere zero on the
ordinary coefficient domain. Equality of all periods of their logarithmic
time forms is necessary and sufficient for a global near-identity conjugacy.
Fixing one ordinary basepoint makes that conjugacy unique.

Theorem 8.1 realizes every resulting modulus on a finitely punctured plane:
the conjugacy-class space in the specified stratum is exactly `m_K^r`.
Theorems 6.1 and 6.4 give the global difference-equation obstruction and its
Bernoulli-operator solution; the cokernel is `K^r`.

Theorem 9.1 constructs exact period moduli invisible modulo every power of a
single noncofinal infinitesimal. A concrete example uses `epsilon=omega^-1`
and `c=omega^(-omega)` inside the surcomplex numbers.

Theorem 11.1 constructs the positive Hahn corrections to an ordinary slow
flow on one fixed holomorphic product chart, with no successive shrinking
of that chart.

## Scope and novelty

The coefficient ring is explicitly `O(D)((t^Gamma))`: all coefficient
functions are holomorphic on the same ordinary domain. Supports and value
groups are set-sized. Sums are strong Hahn sums, not fine-topological limits.
The variable derivative fixes all scalar Hahn constants.

The general exponential/logarithm correspondence for summable automorphisms
and derivations is established work and is not claimed as new. The
manuscript cites Bagayoko, Krapp, Kuhlmann, Panazzolo, and Serra for that
background, and separates its results from classical iterative logarithms
and formal modified differential equations. The Euler coefficients are
known examples, not proposed discoveries.

The global classification, explicit obstruction theory, and higher-rank
invisible-moduli family are proposed contributions. A targeted literature
search did not locate these precise statements in this category; this is
not a verified priority claim. No named published conjecture is claimed
solved. Full mathematical proofs are in the article, but the manuscript has
not been independently refereed or formally checked.

Repository material consulted: the catalogue and relevant analysis and
contour-calculus documentation at commit
`39f2be6667ade51bca2b45daa47e289d69c09764` of
`VladimirReshetnikov/Surreal`. This was not a line-by-line audit of every
repository manuscript. No repository files were changed.

## Build the PDF

Run from this directory:

```sh
sh build.sh
```

A standard TeX Live installation with the packages in the source preamble is
sufficient. No external bibliography, graphics, font files, shell escape, or
network connection is required.

## Run the finite checks

Python 3.10 or later and SymPy are required. The recorded run used Python
3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify.py
```

The checks use exact rational functions and jets modulo `epsilon^8`, along
with separately labelled exact rational identities and finite rank-two
order illustrations. There is no floating point tolerance. Fifty of the
245 assertions are finite lexicographic comparisons; the assertion for all
integers is proved in the article, not inferred from those examples.

Finite checks do not establish arbitrary-rank support finiteness, the global
classification, or the analytic existence theorem. They are transcription
and algebra checks, not a formal proof certificate.
