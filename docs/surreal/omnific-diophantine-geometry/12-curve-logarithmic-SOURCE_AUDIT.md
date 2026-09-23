# Source and claim audit

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/Surreal  
Commit: `89bec380b218c0a5bb865f53a86f5abf7f8fb5ad`

The repository was read through the GitHub connector. The substantive comparison
used the main overview, the report catalogue, the omnific Diophantine guide, and
the main article's Sections 6–7 (including its Euler derivations, detection lemma,
separated-power theorem, and explicit boundary concerning general Weierstrass
cubics). The guide records Question 14.1 and the outstanding smooth-curve issue.
The article source inspected has Git blob SHA:

`47af413cd5f5d186a8c1391514d69e9933034498`

The repository's 51-report collection and all supplementary manuscripts were not
exhaustively audited. We do not certify nonduplication against every historical
or companion source. The repository identifies these manuscripts as AI-assisted
and distinguishes proof review from Lean coverage.

## Existing material, not claimed as new

- Conway normal forms and the normal-form definition of omnific integers.
- Hahn fields and support arithmetic.
- Constant-term retractions and degree/unit facts in one-sided support rings.
- Support-preserving Euler derivations and joint detection of nonconstants.
- Repository separated-power, Pell, binary-form, and unimodular Fermat results.
- Full-class monomial support clearing.
- Classical compactification, Riemann–Roch, the valuative criterion for properness,
  invariant differentials on algebraic groups, and projective invertible quotients.

## Proposed contributions in this manuscript

1. The logarithmic-differential support obstruction and complete smooth affine
   curve classification for arbitrary set-sized ordered exponent groups.
2. The squarefree-superelliptic extension and sharp integral Weierstrass dichotomy.
3. Proper cotangent rigidity, with abelian and semiabelian consequences.
4. Separated-model descent to ordinary integer points.
5. The coordinate-ideal equivalence: invertible, principal, and ordinary rational
   projective point, under the stated rigidity hypothesis.

The last item gives a specific noninvertible two-generated omnific ideal arising
from a nonordinary point on `Y^2 Z = X^3 - X Z^2 + Z^3`.

## External sources actually consulted

- L'Innocente–Mantova, *A factorisation theory for generalised power series and
  omnific integers*, arXiv:1710.07304v5 (22 January 2024).
- Stacks Project, Tags 0BXX (curves/function fields), 0B5B (Riemann–Roch),
  0BY6 (genus), 0C6U (projective line), 0BX5 (proper valuative criterion),
  01ND (projective space), and 01OA (projective bundles).
- Milne, *Abelian Varieties*, course notes v2.00 (2008), for background terminology.

The bibliography contains specific URLs. Targeted web searches did not locate an
exact precedent for the main combined theorem package, but their coverage was
incomplete and often noisy. No claim of exhaustive literature search or certified
priority is made.

## Validation performed

- Written proof development and internal mathematical review.
- Exact SymPy verification of the cubic certificate, singular parametrization,
  sample differential-ideal certificates, and displayed series coefficients.
- Seeded finite-support Euler-law checks over lexicographically ordered Z^2.
- LaTeX compilation and PDF layout inspection.

## Validation not performed

- Independent mathematical peer review.
- Lean formalization or repository build.
- A complete search of the published literature and every repository manuscript.
- Algorithmic verification of all infinite Hahn supports or all valuation ranks.

## Critical hypotheses retained

The coefficient field is algebraically closed of characteristic zero in the
abstract Hahn theorems. Affine curves are smooth and integral. The support ring
uses nonpositive Hahn exponents (nonnegative Conway exponents), not the finite
valuation ring. The proper theorem requires global cotangent generation.
Omnific descent uses separatedness and a compatible constant-term retraction.
Projective coordinates are treated through invertible ideals, not merely through
nonzero tuples. Primitive and unimodular are not identified.
