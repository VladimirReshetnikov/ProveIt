# Source review and novelty boundaries

Review date: September 24, 2026.

## Pinned ProveIt snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`

Read through the connected GitHub tools:

- `README.md`: repository map and theorem-status overview.
- `Algebra/JacobianConjecture/README.md`: the explicit polynomial map,
  determinant, collisions, symmetry, and formal-statement boundary.
- `Algebra/JacobianConjecture/Research/README.md`: exact stable reductions,
  degree frontier, and equivariant rigidity statements.

The article makes no new claim to discovering the map or disproving the
Jacobian conjecture. The determinant is rederived with a short coordinate
calculation and independently checked by exact symbolic differentiation.
The article does not claim to audit all of ProveIt or rerun its Lean build.

## Existing complex geometry

Shuhong Gao, *Counterexamples to the Jacobian conjecture in dimensions
greater than two*, arXiv:2608.00222v1 (2026).
https://arxiv.org/html/2608.00222v1

Theorems 3.3–3.4 already give the generic degree and complete complex fiber
stratification. The article's projective simple-root argument reproduces
that geometric result for use in arithmetic proofs; it is not relabeled new.

## Existing finite-field and Hasse research

Repository: https://github.com/royvanrijn/jacobian-research
Commit: `caf5685db1099cb90e608556d4b8d825734f29cb`

- `research/archive/legacy-notes/FINITE_FIELD_VALUE_DISTRIBUTION.md`:
  existing cubic inverse, exact odd-characteristic histograms, characteristic
  three and characteristic two finite-field laws, and refinements.
- `research/archive/non-elliptic/verified/INTEGRAL_HASSE_JACOBIAN_ONE.md`:
  a different integral determinant-one map whose geometric degree-five
  fiber has integral local points everywhere but no rational point.

Both were read through connected GitHub tools. They are primary public
research notes, not independently established peer-reviewed publications.
Their results are credited as existing work. The second note is used only
for comparison and is not assumed in any proof in the article.

Additional targeted repository searches for integral/cubic/profinite and
2-adic image material did not locate the same split-plane classification or
the exact dyadic 11/32 measure. Those searches are not a comprehensive
worldwide novelty audit. No historical priority is certified.

## External theorem used

James S. Milne, *Algebraic Number Theory*, version 3.08 (2020),
Theorem 8.31 and Example 8.36:
https://www.jmilne.org/math/CourseNotes/ANT.pdf

The Chebotarev statement and its cubic application were checked in the
source; page 148 of the PDF (printed page 147) was also visually inspected.
Only qualitative Chebotarev is used. The elementary Bertrand prime bound
is used solely for the optional quantitative sieve estimate; the basic
zero-density conclusion and explicit integral counterexamples do not use it.

## Candidate new refinements and limitations

The article contributes independent proofs of an explicit split integral
Hasse family, a complete primitive-difference criterion, density
27/(4*pi^2), Zariski density in the plane C=2, persistence with the same
parameter density over any fixed S-integer ring, and the exact integral
2-adic law (21,7,3,1)/32. Their priority remains provisional.

Do not confuse:

- rational preimages with integral preimages;
- Zariski density in a plane with density in all of affine three-space;
- density of ordered root parameters with density of target coefficients;
- finite fields F_(2^m) with rings Z/(2^m);
- exact Python/SymPy checks with Lean/Rocq kernel proofs.
