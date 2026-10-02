# Provenance and attribution

## Date and repository checkpoint

Sources were inspected on October 1, 2026.

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned recursive-tree checkpoint:
`1f1981f682b2878bde51a6ad40c22777f362fc05`.

The connected GitHub tools were used to inspect the root, the Oeis
folder, the recursive tree, repository search results, and the pinned
transseries README:

https://github.com/VladimirReshetnikov/ProveIt/blob/1f1981f682b2878bde51a6ad40c22777f362fc05/Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md

The README documents coefficient identities, real Lambert cores,
remainder transport, and staircase inversion, including explicit
formalization boundaries. No claim here treats the README's inventory
as a machine proof of this report's analytic partition asymptotics.
An A097356-specific repository search and a search of the inspected tree
returned no match. This is a bounded duplicate check, not proof of the
absence of every related result in the whole repository.

No repository write, commit, issue, or pull request was made.

## OEIS entries directly inspected

- https://oeis.org/A097356 : the partition definition and the January 8,
  2024 conjectured lower constant attributed to Vaclav Kotesovec.
- https://oeis.org/A206226 : square-restricted partitions, existing
  leading amplitude, general quadratic family, and dilogarithmic equation.
- https://oeis.org/A206227 : the positive linear shift and existing amplitude.
- https://oeis.org/A206240 : the negative linear shift and existing amplitude.
- https://oeis.org/A258268 : existing exponential-growth constant.

The first 54 terms of A097356 and first 17 terms of A206226 are embedded
as exact transcription checks in verify.py. The new counts are generated
independently by integer dynamic programming; no OEIS b-file is needed
at runtime.

## Primary mathematical sources

E. Rodney Canfield, From Recursions to Asymptotics: On Szekeres' Formula
for the Number of Partitions, Electronic Journal of Combinatorics 4(2)
(1997), R6. The leading formula and its parameter normalization were
inspected; the PDF's first two pages were also visually inspected.
https://www.combinatorics.org/ojs/index.php/eljc/article/view/v4i2r6

Dan Romik, Partitions of n into t sqrt(n) parts, European Journal of
Combinatorics 26(1) (2005), 1-17. DOI 10.1016/j.ejc.2004.02.005.
The author's publication listing and paper were consulted for the
classical restricted-partition setting and attribution.
https://www.math.ucdavis.edu/~romik/data/uploads/papers/pofnk.pdf

Tiefeng Jiang and Ke Wang, A generalized Hardy-Ramanujan formula for the
number of restricted integer partitions, arXiv:1805.06108. Cited for a
two-restriction continuation, not used as an undeclared proof dependency.
https://arxiv.org/abs/1805.06108

NIST DLMF, section 24.8, Bernoulli Fourier series. Used for the
Bernoulli-zeta coefficient identity underlying the rational tail bound.
https://dlmf.nist.gov/24.8

## Result boundaries

Classical: the leading restricted-partition saddle and OEIS amplitudes.

Developed with proofs in this report: the explicit uniform all-orders
bounded-offset operator; phase polynomial conversion; sharp envelope
interpretation; eventual exactly-three endpoint violations; normalized
limiting distribution; leading summatory phase law; smooth inverse
coefficients; global phase-aware inverse and interior all-orders reversion.

Computed: exact partition integers, high-precision numerical comparisons,
and exact rational interval certificates for the sign inputs.

Not established: global first-discovery priority; the smallest effective
stable block; a full exponentially improved transseries; all-orders
uniform inverse switching layers; a Lean or Coq formalization.

No third-party paper PDFs, repository source files, or font files are
redistributed. Bibliographic links identify the consulted sources.
