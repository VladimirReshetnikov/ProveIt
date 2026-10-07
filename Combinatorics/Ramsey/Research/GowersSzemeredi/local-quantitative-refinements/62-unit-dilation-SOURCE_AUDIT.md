# Source and scope audit

Research date: 6 October 2026. This is a record of source inspection, not an
independent referee report.

## Repository checkpoint

Repository: `VladimirReshetnikov/ProveIt`.

Inspected commit reference:

`17123532a2de638477dce1c92eb0b0b20a247d2f`

Repository directory, search, and file reads were performed through the
connected GitHub tools. The following files supply the relevant comparison.
Paths are relative to `Combinatorics/Ramsey/`.

| File | Inspected blob | Relevant content |
|---|---|---|
| `Research/GowersSzemeredi/local-quantitative-refinements/README.md` | `689dbd37cf1a495a38124a62c20aff90460ca7a5` | Research map, source-17 prime-modulus restriction, source-29 fixed-field restriction, and notices of later staged drafts. Relevant passages were re-read at the pinned commit. |
| `Lean/GowersSzemeredi/Definitions.lean` | `97113b7afa6925a2dd4b76641eeaeff09597ab6a` | Ordered additive tuple count, respected tuple count, and the division-free `GammaHomOfOrder` definition; relevant range 290-385. |
| `Lean/GowersSzemeredi/Sections08_09.lean` | `0fb6e0a1de3f046f436747603f7eeb06f8d1f074` | `lemma_9_3` and `corollary_9_4`; relevant range 60-110. |
| `Lean/GowersSzemeredi/Proofs09Restriction.lean` | `29bb4178fbec83d177200ce2c2978a3c0b245112` | Existing proof module. Its opening section was inspected, and code search returned `theorem lemma_9_3_holds : lemma_9_3 := by`, using a zero-dimensional instance of the Section 15 restriction argument. |

Pinned root:
https://github.com/VladimirReshetnikov/ProveIt/tree/17123532a2de638477dce1c92eb0b0b20a247d2f/Combinatorics/Ramsey

The source-17 summary states prime-modulus retention
`alpha^m eta^(m-1)/(2(m+2)^m)` and the order-eight coefficient
`alpha^16 eta^15/(2*18^16)`. The source-29 summary explicitly distinguishes
its fixed-field result from the all-moduli interface.

The present contribution is an all-cyclic-modulus extension with independent
domain and target moduli, a unit-averaged response, and a weighted arithmetic
error. The existing prime-field method is credited as a predecessor, not
represented as newly discovered here.

## Gowers paper

W. T. Gowers, *A new proof of Szemeredi's theorem*, Geometric and Functional
Analysis 11 (2001), 465-588.
DOI: `10.1007/s00039-001-0332-9`.

Publisher bibliographic record:
https://link.springer.com/article/10.1007/s00039-001-0332-9

Inspected primary-paper copy:
https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The PDF has 124 pages. Section 9, including the approximate-homomorphism
definition and Lemma 9.3, was read through parsed text and page screenshots.
In particular, zero-indexed PDF pages 50-51 (printed pages 515-516) establish
the ordered-tuple convention and the retained coefficient
`(alpha eta/4)^(2^19)`. The subsequent filter proof was also consulted.
The PDF itself is not redistributed in this package.

## Rosser-Schoenfeld input

J. Barkley Rosser and Lowell Schoenfeld, *Approximate formulas for some
functions of prime numbers*, Illinois Journal of Mathematics 6 (1962),
64-94. DOI: `10.1215/ijm/1255631807`.

Publisher record:
https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-6/issue-1/Approximate-formulas-for-some-functions-of-prime-numbers/10.1215/ijm/1255631807.short

Theorem 15 supplies the classical inequality, valid for every integer n>=3,

```
n/phi(n) < exp(gamma) loglog(n) + 2.50637/loglog(n).
```

The bibliographic metadata and the statement in searchable primary-research
citations were checked. Direct access to the complete publisher PDF and an
alternate PDF mirror was unsuccessful in this session; a full re-reading of
that proof is not claimed. The external input is explicitly isolated in the
article. The all-modulus polynomial theorem, exact weighted degeneracy
formula, and detector obstructions do not depend on it.

## Limits of comparison

The investigation used the repository's research summary to avoid duplicating
its many nearby directions. It did not independently re-prove every earlier
draft or inspect every line of the entire combined research article. Nor was
an exhaustive literature search establishing publication priority completed.
The article therefore asserts written mathematical results and explicit
comparisons with inspected interfaces, not worldwide novelty certification.

The theorem is not conditional on the correctness of another unpublished
research draft: the necessary filter, arithmetic, and extraction arguments
are written out in the delivered article. No GitHub write action was used.
