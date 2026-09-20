# Research status and claim boundaries

Date: 20 September 2026.

## Claim presented

The article supplies a complete mathematical argument for all assertions of
**Cigler's Conjecture 16, arXiv:2111.14492v3, Section 6, pp. 21–22**:
polynomiality after the prescribed normalization; degree `(k-1)n`; strict
coefficient positivity after sign adjustment; reciprocity; and the even- and
odd-shift stable-coefficient formulas for every degree `0 <= j <= n`.

It additionally gives the exact first disagreement at `j=n+1`, with deficit
`binomial(n+floor(k/2),floor(k/2)-1)` for every `k >= 2`. The all-index result
is a proof claim, not a conclusion drawn from the computational test range.

This is an **unrefereed AI-assisted research draft**. It has not been verified
in Lean or another proof assistant, and no independent expert review has
occurred as part of this package. The ordinary mathematical proofs are offered
for scrutiny. They should not be relabelled as independently established
results merely because the finite tests pass.

## Proof map

| Result | Location | Mechanism |
|---|---|---|
| Source-moment identities | Section 2 | Binomial expansion and Laurent bases |
| Auxiliary Gram identity | Section 3 | Monic orthogonal polynomials |
| Four parity factorizations | Section 4 | Explicit block row operations |
| Strict positivity and reciprocity | Section 5 | Bidiagonal factorization, Cauchy–Binet, coefficient lower bounds |
| Small determinant evaluations | Section 6 | Proved Christoffel identity and confluent alternants |
| Stabilization and first defect | Section 7 | Unique lowest-degree nonconstant numerator contribution |
| Fixed-shift rationality and analytic convergence | Section 9 | Finite exponential-polynomial expansions |
| Product evaluation at `t=1` | Appendix A | Leading alternating term of a hyperbolic-sine determinant |

Every determinant identity essential to the main proof is derived in the
article. The classical general framework is credited to the literature, but
no unproved theorem from the manifest is used.

## Explicit exclusions

The rectangular-Schur identity in Section 10 is **experimental and unproved
here**, despite its successful finite tests. It is not needed to establish
Conjecture 16. The paper also does not claim a full solution of Cigler's
Conjectures 17 or 18, or minimality of the coarse recurrence denominator.

No unimodality or log-concavity theorem is claimed: the displayed example
`H_4(2;t)` has coefficient valley `5,4,5`. Exceptional parameters are treated
through polynomial identities, not substitution into a zero denominator.
The determinant reduction is a fixed-shift size reduction, not a claim that
expanded output can be computed in time independent of its length.

## Nonduplication and literature status

The related manifest entry concerns different moments `a_n(t)` and different
numbered conjectures, 13–15 in Section 5. The chosen `c_n(t)` question is
Conjecture 16 in Section 6. The present paper does not alter or certify the
other reports listed in the manifest.

The primary paper was directly inspected, including images of the formula
pages. A targeted search did not locate a later solution to this particular
conjecture. This is a bounded negative search result, **not** proof that no
such work exists. No absolute claim of first discovery is made.

## Reproducibility checks

All reported checks passed. The main results are in `data/verification.json`;
supplementary results are in `data/additional_verification.json`. Their console
outputs are also included. The source moments, matrix-corner determinants, and
small alternants are computed by distinct routines, although they share a
checked exact Bareiss determinant implementation.

The PDF was rebuilt from the included source, with no undefined references or
overfull-box warnings, and reviewed as rendered page images. Successful TeX
compilation and clean page layout are document checks, not mathematical proof
verification.
