# Source audit

Audit date: 1 October 2026. This was a targeted search, not an exhaustive
literature review. The absence of a result in search output is not proof of
absence from the literature or repository.

## Published target

Richard P. Brent, M. L. Glasser, and Anthony J. Guttmann,
*A Conjectured Integer Sequence Arising From the Exponential Integral*,
Journal of Integer Sequences 22 (2019), Article 19.4.7.

- Journal page: https://cs.uwaterloo.ca/journals/JIS/VOL22/Brent/brent21.html
- Journal PDF: https://cs.uwaterloo.ca/journals/JIS/VOL22/Brent/brent21.pdf
- Preprint: https://arxiv.org/abs/1812.00316

Relevant journal numbering: Corollary 9 (analytic product expansion), Conjecture
10 (integrality), Remark 11 (negativity and mod-32 observations), Lemma 14
(independent rational coefficient recurrence), and Theorem 17 (`k! r_k` integral).
The conjecture and observation were also visually checked in the PDF on printed
page 10. The source's published proof of the all-orders expansion is an input
in the attached article. Its arithmetic conjecture and congruence are proved by
a different nonlinear recurrence in the attached article.

The OEIS entry uses older preprint numbering. The final article deliberately
uses the journal numbering and explains the difference.

## OEIS

- https://oeis.org/A321941
- https://oeis.org/A321941/internal
- https://oeis.org/A000262

At inspection, A321941 continued to describe `r_k` integrality as conjectural.
The thirteen displayed values were used as a finite consistency check. This
status is the wording of the inspected entry, not an exhaustive determination
that no proof exists elsewhere. A000262 supplies the natural combinatorial
context of the growing companion sequence.

Searches for A321941 with “proof”, “integrality”, and “congruence”, and searches
using the authors and paper title, did not locate a later proof. This observation
is not a guarantee of priority.

## ProveIt

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit:

    0a6d798c5f39775b2fb4d85fef643fef996c87cf

Relevant inspected resources:

1. Repository README and recursive tree metadata.
2. `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md`
3. `Analysis/FabiusFunction/Lean/FabiusFunction/QuadraticCoreCatalan.lean`

Pinned links:

https://github.com/VladimirReshetnikov/ProveIt/blob/0a6d798c5f39775b2fb4d85fef643fef996c87cf/Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md

https://github.com/VladimirReshetnikov/ProveIt/blob/0a6d798c5f39775b2fb4d85fef643fef996c87cf/Analysis/FabiusFunction/Lean/FabiusFunction/QuadraticCoreCatalan.lean

The connector's repository search for `A321941` returned no indexed matches.
The full consolidated transseries volume and every repository file were not
read. The crosswalk in the article is prospective: existing Catalan algebra,
formal coefficient uniqueness, and inversion infrastructure are relevant,
but they do not constitute a formal certificate for the new results.
No Lean or Rocq build was performed.

## Claims and boundaries

The article supplies proofs for integrality/evenness, the polynomial deformation,
the mod-32 refinement, the stated denominator theorems, and inverse arithmetic.
It does not prove negativity of all later coefficients. It does not establish
uniform analytic parameter asymptotics, effective remainder constants,
convergence, or complete exponentially small sectors. Its search-based novelty
assessment and the correctness of its original proofs remain open to independent
expert review.

No third-party article, repository source file, or font file is redistributed.
