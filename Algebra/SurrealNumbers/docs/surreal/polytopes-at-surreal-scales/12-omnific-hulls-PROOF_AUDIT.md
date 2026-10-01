# Mathematical proof audit

This records the internal review performed in preparing the draft. It is not
an independent referee report or a kernel-checking record.

## Main dependency chain

1. The omnific splitting is Pi + Z, where Pi is a real vector space and every
   nonzero member is infinite in magnitude. It supplies floors, remainders,
   and the finite-element lemma.
2. For a set-sized rational subspace H of Pi, H + Z is a Z-group. Inclusions
   between these groups preserve and reflect ordinary congruences and are
   elementary by classical Presburger quantifier elimination.
3. Ordinary bounded integer optimization is expressed by one fixed
   Presburger sentence. Transfer gives existence for fixed ordinary
   objectives without declaring an omnific box finite.
4. The graph lattice uses BOTH u and Au. Dickson's lemma gives a finite
   Graver set. Its conformal decomposition is transferred as a fixed finite
   coefficient formula, never as an infinite number of unit steps.
5. A used Graver direction is a feasible unit move. Finite signed sums prove
   the local-to-global criterion for arbitrary surreal objectives.
6. Rational objective chambers supply finitely many unique optima. Finite
   strict separation proves that they generate the entire hull; this occurs
   BEFORE applying finite-polytope edge or normal-fan arguments.
7. At a generic optimum, rows of ordinary-bounded slack have full rank.
   Otherwise a rational null vector supplies a Graver direction feasible in
   both signs, contradicting generic optimality.
8. These rows yield the bounded-offset basis formula. Adjugate congruences
   decide candidate integrality; rational linear tail signs and ordinary
   constant inequalities decide feasibility.
9. Finitely many exact objective comparisons determine all faces. A
   parameter-free existential Presburger sentence realizes the same finite
   data over the ordinary integers.
10. A real linear form on omnific points is either purely-infinite-plus-real
    with infinite magnitude, or an ordinary value in its integer image.
    Dense irrational images therefore give missing maxima and missing
    surreal suprema at excluded real thresholds.

## Corrections and pitfalls explicitly avoided

- Bounded omnific intervals can be proper classes. No enumeration or ordinary
  compactness argument is used for them.
- The full class Oz is not passed as a set-sized model to a compactness
  theorem. Finite parameters and witnesses are localized in H + Z.
- Positivity of an omnific decomposition coefficient implies it is at least
  1; this is what makes a used ordinary direction a feasible unit step.
- No termination claim is made for repeated unit augmentation from an
  arbitrary infinite starting point.
- A candidate is close to a basis intersection, not necessarily to a feasible
  vertex of the original linear relaxation.
- Tail signs alone are not enough: zero tails require constant inequalities,
  and candidate integrality requires ordinary residues.
- Same-matrix descent preserves finite face data, not metric scales or a
  complete ordered-field type of the parameters.
- The irrational example with threshold 1/2 has NO surreal supremum. Its real
  limiting value 1/2 is not a surreal least upper bound.
- No order-topological nonclosedness is inferred from an ordinary real
  approximating sequence.
- Irrational normals do not make every individual instance fail: the
  threshold-zero example has four omnific vertices.
- The threshold-one example has an attained principal objective, but its
  equality face is parameterized by u in Pi with -omega <= u < omega.
  Replacing u by (u + omega)/2 proves secondary nonattainment. The objective
  perturbation omega^(-2)*y cannot compensate for a positive real loss in
  the principal objective.
- The positive result extends to arbitrary integer parts; the real-linear
  splitting used in the negative argument is not assumed for all such parts.

## Finite evidence

All default assertions of `verify.py` passed. Counts and arithmetic scope are
in `verification_results.json`. General theorem completeness does not follow
from these counts; it follows from the mathematical arguments and their
stated classical prerequisites.

## Remaining assurance boundary

No independent proof review, new Lean formalization, or exhaustive novelty
certification has been performed. The work should be reviewed on that basis.
