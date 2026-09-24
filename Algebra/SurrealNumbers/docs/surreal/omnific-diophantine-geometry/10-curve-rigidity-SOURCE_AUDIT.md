# Source and novelty audit

Research date: 23 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `4cdeaec43ff1692ed2ad9f5bdf761a41872975a5`.

Principal source:
`docs/surreal/omnific-diophantine-geometry/article.tex`.
Its content blob at the pin is
`4c26f4e4bee62f76428d7c69adf4aabe5af5ec53`.

The direct article excerpts inspected were source lines 1–130,
1350–1690, and 2910–3100. They include the introductory scope,
binary-form/Pell/norm rigidity, the support-preserving Euler derivations,
the separated-power proof, and the continuation questions. The associated
README provided the larger statement inventory. The root README,
`docs/README.md`, and the set-sized-quotient report's README were also read.
This was not an exhaustive read of the repository or its history.

Question 14.1, source label `odg:q:affine`, asks which affine varieties
and curves have no additional omnific points and identifies
`Y^2 = X^3 + aX + b`, with `a != 0`, as a next test. The source expressly
does not certify that its continuation questions are open in the entire
published literature.

## Existing ingredients versus proposed contributions

Existing ingredients, not counted as new:
- Normal forms, Hahn arithmetic, the nonnegative-support ring, degree,
  constant-term retraction, and the constant-unit lemma.
- The family of Euler derivations and separation of a nonconstant by
  choosing a rational linear functional on its exponent group.
- The repository's separated-power rigidity, torus/unit arguments,
  unimodular Fermat result, and full-class monomial clearing.
- Kähler differentials, the valuative criterion for properness,
  Riemann–Roch and smooth completion for curves, and invariant
  differentials on algebraic groups.

Proposed contributions in this manuscript:
- A squarefree-superelliptic extension using a Bézout differential
  certificate, including an explicit nonsingular-cubic certificate.
- The two-ring evaluation obstruction for global one-forms and its
  proper-target rigidity theorem.
- The exact arbitrary-rank, arbitrary-support smooth affine-curve
  dichotomy: only the affine line admits nonconstant points.
- The exact arithmetic criterion and polynomial bijections between
  every nonempty affine-line constant-term fiber and the purely
  infinite ideal.
- Abelian, semiabelian, and quasi-finite-target rigidity, and the
  corresponding unimodular homogeneous-coordinate consequence.

The polynomial-ring special case of maps from an affine line to a
positive-genus curve is standard and is not claimed as original.

## Primary external sources inspected

1. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for
   generalised power series and omnific integers*, arXiv:1710.07304v5
   (22 January 2024), Advances in Mathematics (2024), article 109513.
   https://arxiv.org/abs/1710.07304
   https://arxiv.org/html/1710.07304v5
   https://doi.org/10.1016/j.aim.2024.109513
   Used for modern generalized-series/omnific context, not as a source
   of the new curve theorem.

2. The Stacks Project, tag 00RM, Differentials.
   https://stacks.math.columbia.edu/tag/00RM
   Used for the universal property and functoriality of differentials.

3. The Stacks Project, tag 0BX4, Valuative criteria, Lemma 29.43.1.
   https://stacks.math.columbia.edu/tag/0BX4
   Explicitly allows all valuation rings, which is essential for the
   arbitrary-rank assertion.

4. The Stacks Project, tag 0B5B, Riemann–Roch.
   https://stacks.math.columbia.edu/tag/0B5B
   Used for the usual curve Riemann–Roch consequences; the basepoint-free
   canonical-bundle deduction is spelled out in the manuscript.

5. The Stacks Project, tag 0BXX, Curves and function fields.
   https://stacks.math.columbia.edu/tag/0BXX
   Used for smooth projective completion and the projective model of a
   one-variable function field in characteristic zero.

6. J. S. Milne, *Abelian Varieties*, course notes, version 2.0, March 2008.
   https://www.jmilne.org/math/CourseNotes/AV.pdf
   Chapter IV, Propositions 6.4–6.7, printed page 152 (PDF page 158).
   The relevant page was inspected as an image as well as parsed text.
   Used for invariant differential forms and the trivial cotangent
   bundle of an abelian variety.

## Search limitations

Targeted searches combined “omnific”, “elliptic”, “genus”, “Hahn”,
“generalised power series”, “curves”, “derivations”, and “abelian
varieties”. Results were uneven and often irrelevant. No identical
statement was verified in the inspected sources. This is not evidence
that none exists. Native repository code search returned no matches for
“elliptic” despite its presence in direct file reads, so that search
cannot support any completeness claim.

The manuscript does not claim to settle a famous named conjecture,
does not assert the current status of Conway's factorization/refinement
questions, and does not claim worldwide priority. A specialist
literature review may locate antecedents or a more general known result.

## Verification boundary

The new results have written proofs. They have not been checked in Lean
or another proof assistant, refereed, or independently reviewed. The
finite verification script checks exact identities and finite-support
models only. It does not establish the infinite-support or geometric
arguments. No repository build was performed for this manuscript, and
no existing repository declaration is being presented as a formal proof
of a new statement here.

The inspected repository is unchanged. The delivered files are a new,
standalone research package.
