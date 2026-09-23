# Source and proof audit

Date: 23 September 2026.

## 1. Exact repository baseline

Repository: `VladimirReshetnikov/Surreal`.
Commit: `4cdeaec43ff1692ed2ad9f5bdf761a41872975a5`.
Main source: `docs/surreal/omnific-diophantine-geometry/article.tex`.
Blob: `4c26f4e4bee62f76428d7c69adf4aabe5af5ec53`.

The main source was read through the connected GitHub tool at this commit.
Relevant inspected source line ranges include 1–230, 1000–1200,
1460–1670, 2650–2860, and 2980–3125. Its README and the introduction of
`docs/FORMALIZATION.md` were also read. This is not an exhaustive audit of
all manuscripts, unmerged companions, historical commits, or Lean modules.

The decisive source question is Section 14, Question 14.1,
label `odg:q:affine`. It asks about rigid affine varieties and curves and
singles out Y^2 = X^3 + aX + b with a != 0. The report expressly does not
claim that its continuation questions are known open literature problems.

## 2. Material already in the inspected repository

The constant-coefficient retraction, unit calculation, support-preserving
Euler derivatives and their detection property, separated-power rigidity,
the special unimodular Fermat result, primitive constant-direction theorem,
and finite-support specialization are prior repository material. This article
re-proves the local tools for clarity and does not claim priority for them.

The Pythagorean family (t^2-1,2t,t^2+1), including its unimodularity witness,
is also prior repository material and is identified as such.

## 3. Proposed extensions supplied with proofs

- Theorem 4.1: arbitrary squarefree superelliptic equations, including an
  explicit certificate for the general nonsingular cubic and the borderline
  squarefree quadratic case.
- Theorem 5.1: an abstract differential-annihilation theorem for two rings in
  one field, one a valuation ring, using properness and global tensors.
- Section 6: cotangent and symmetric-differential rigidity criteria.
- Section 7: the complete smooth geometrically integral curve classification
  over R and C for nonnegative-support Hahn points.
- Section 8: exact ordinary-integrality fibers and a finite-support witness
  principle for every nonordinary omnific point on such an affine curve.
- Section 9: abelian and semiabelian rigidity; exact vector-group kernel for
  points of a smooth connected commutative algebraic group.
- Section 10: general positive-genus rigidity for unimodular homogeneous tuples.

The classification resolves only the explicitly stated smooth geometrically
integral part of the broad repository curve question. Ordinary integer point
existence remains separate from geometric affine-line classification.

## 4. Classical external dependencies

The article's bibliography records the sources precisely:

- L'Innocente and Mantova, Advances in Mathematics 442 (2024), 109513:
  Hahn/Conway and omnific normal-form background, not the new curve theorem.
- Stacks Project tags 01KF, 02AT, 01V4, 0BXX, 0B5B, 01OA, 01PR:
  proper/valuative existence, differentials, smooth cotangent bundles,
  curve completion, Riemann–Roch, projective bundles, and ample line bundles.
- J. S. Milne, Algebraic Groups (2017), Theorem 8.27, Corollaries 14.33 and
  16.15: Barsotti–Chevalley and characteristic-zero commutative affine-group
  structure. The affine hypothesis in the use of Corollary 16.15 is retained.

These are primary mathematical references. No secondary webpage is used as a
substitute for a proof of the new conclusions.

## 5. Critical proof-review boundaries

1. The Conway-sign convention is B = support >= 0, O = support <= 0,
   valuation v = -degree, with B intersect m = 0.
2. D(O) is contained in m, not merely O. This follows from support
   preservation and deletion of the zero coefficient.
3. Constancy uses the entire family of rational-linear Euler characters.
   One character can kill a nonconstant series.
4. Properness extends the K-point to the valuation ring. The B-point and
   valuation-ring point may use different affine charts. Only their global
   differential contractions are compared.
5. K is not assumed equal to Frac(B) at a fixed stage. B is not assumed
   normal, local, a valuation ring, or a Bezout domain.
6. The elementary certificate lies in the strict ideal I. This handles the
   degree equality endpoint m = deg(F) = 2.
7. Group-point splitting via constant coefficients does not assert algebraic
   splitting of an extension of algebraic groups.
8. The projective theorem requires a finite unit-ideal witness, not merely
   absence of a common nonunit divisor.
9. Non-normality is demonstrated inside Frac(B) in a workspace with a scale
   H larger than all ordinary integers, explicitly clearing the negative
   tail of sqrt(omega^2+1). It is not inferred merely from an integral root
   lying in a larger containing field. This is not itself a counterexample
   to normalization lifting for a constant curve.
10. All scheme constructions and linear-functional families are set-sized.
    Full surreal statements are assembled stagewise.

## 6. Computation and typesetting

The exact-check script was run successfully. The included report records
12,874 assertions using Python 3.13.5 and SymPy 1.14.0. Most assertions test
finite degree inequalities or finite Hahn-algebra operations; they are not
12,874 independently verified theorems.

The PDF was compiled with pdfLaTeX through repeated runs until cross-references
stabilized. The final build has 29 pages, no unresolved references/citations,
and no overfull boxes. Page images were rendered and visually inspected for
layout. These checks establish artifact integrity, not theorem correctness.

## 7. Unresolved matters and novelty

The proofs have not been independently refereed or formalized in Lean.
Targeted literature searches and the inspected source portions did not locate
an earlier statement of the combined theorem package. They do not establish
priority or justify a claim of a certified breakthrough.

The article does not settle arbitrary higher-dimensional varieties, arbitrary
singular curves, primitive non-unimodular Fermat tuples, or general Conway
factorization/refinement questions. The remaining questions are labeled as
boundaries of this work, not as newly certified open literature problems.
