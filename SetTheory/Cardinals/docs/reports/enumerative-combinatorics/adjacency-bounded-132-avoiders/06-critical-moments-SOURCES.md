# Source and provenance ledger

## Repository boundary

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit, resolved through GitHub's main-branch reference on 30 September 2026:

`cb1646dc442724f8e298cf259195b6c308367d80`

Report directory:

`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/`

Pinned directory URL:
https://github.com/VladimirReshetnikov/ProveIt/tree/cb1646dc442724f8e298cf259195b6c308367d80/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders

Inspected source files:

1. `README.md`, blob `9b6865915b549427272025beaf2826d59131b6d1`.
   Scope ledger, especially source lines 231–249, explicitly leaves convergence of the
   centered half-moment and corrections to subcritical moments open. The pinned range
   was checked again after drafting. This is the basis for the repository-relative
   resolution claim.
2. `article.tex`, blob `c673f447a22396f5c66b36b4ce8141acc0ceee3d`.
   Relevant portions are Parts III and IV; the source was inspected through the GitHub
   connector. Part III introduces the largest-jump deficit and limiting law; Part IV
   treats the macroscopic profile and supercritical leading moments.
3. `code/05-macroscopic-deficits-model.py`, blob
   `f0248e0d6181200257e2949c1a8fa8f9fecf5617`.
   Inspected in full at the pin. Its Mayama–Akita endpoint-state recurrence and
   first-entry formula informed the finite verification implementation. The new
   implementation does not use its unrestricted-state shortcut, supplies a derivation
   in Appendix A, and is independently checked against exhaustive generation.

## Exact upstream interfaces used by the proofs

- Part III: positive-integer limit D, its algebraic PGF, the tail
  P(D > k) = 3/sqrt(pi k) + O(k^(-3/2)), and the O(n^(-1/2)) total-variation bound.
  Relevant source labels include `lj:thm:main`, `lj:sec:pgf`, `lj:sec:singularity`,
  `lj:sec:tv`, and `lj:cor:sharp-tv`. The exact TV leading constant is NOT assumed.
- Part IV: Theorem 38.1, source label `mj:thm:profile`, giving the pointwise bulk profile
  sqrt(n) P(D_n > un) -> Psi(u), with Psi(u)=0 at and above u=1/2.
- Open problem references: `mj:sec:q-centered`, the Part IV scope discussion, and the
  README ledger above. The new abstract theorem requires no result about the fixed-m
  spectral growth constants.

These are mathematical inputs from an unrefereed AI-assisted report, not formally
checked declarations. The supplied article makes this dependency explicit. No complete
upstream report or external paper is redistributed in this package.

## Public primary papers

Nathaniel Nadler, *On 132-Avoiding Permutations with an Adjacency Constraint*,
arXiv:2604.22135v1, 24 April 2026.
https://arxiv.org/abs/2604.22135v1

Teruki Mayama and Dai Akita, *Finite-state enumeration of adjacency-constrained
132-avoiding permutations*, arXiv:2605.23519v1, 22 May 2026.
https://arxiv.org/abs/2605.23519v1

The primary arXiv records and relevant HTML were checked on 30 September 2026.
They provide problem context and the endpoint-state enumeration method. We do not
attribute the largest-jump critical-moment results to them.

## Novelty boundary

The investigation compared the pinned report's explicit open-problem ledger with the
new deductions and made targeted public searches for the relevant permutation and
critical-moment terms. This does not establish that the abstract transfer principle,
the constants, or related conclusions have never appeared elsewhere. There is no
claim of exhaustive bibliographic coverage, external peer review, or established
publication priority. Claims of progress are relative to the pinned repository.

## Artifact provenance

The article, new proofs, finite checks, numerical programs, and figures were generated
for this request. No repository write was performed. Finite counts are exact integers;
quadrature output is explicitly non-certified. The build and all finite/numerical
checks described in the article were run, and the resulting PDF pages were rendered
and visually reviewed before delivery.
