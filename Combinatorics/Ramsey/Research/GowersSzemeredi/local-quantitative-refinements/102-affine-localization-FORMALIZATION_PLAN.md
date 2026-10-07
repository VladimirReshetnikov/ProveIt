# Formalization plan and proof boundary

## Current state

All theorem proofs are in `article.tex`; none was kernel-checked in this
session. The package deliberately contains no uncompiled Lean theorem skeletons,
`sorry` placeholders, or new axioms. Exact Python tests are finite corroboration,
and the optional mixed-integer solver uses floating point.

## Semantics to preserve

An affine partition is a finite, pairwise-disjoint family of nonempty **actual
subsets**, each certified as an affine F_q-subspace. A cover is not a partition.
Distinct descriptions of the same subset must not count as distinct cells.
Optimal partition enumeration is of unordered subset families in fixed
coordinates, not modulo geometric automorphisms.

Fields may have nonprime order. The scalar quadratic and phase-equivalence
results require odd characteristic. The cross-square geometry works for every
field with q>2, and its two-optimizer classification requires q>3. Do not use
an additive character's injectivity in extension fields: the proof uses full
F_q scalar closure instead.

## Proposed development order

1. **Partition invariant API.** Define P(X), A(f), fiber additivity, transport,
   and product upper bounds. Pullback equality needs both inverse images and
   intersection with a linear section of a surjective map.
2. **Orthant containment.** Two proper affine hyperplanes cannot cover a
   positive-dimensional affine space when q>2. Apply independently to each
   coordinate equation x_i*y_i=0.
3. **Constructed cyclic partition.** Give actual lines and the singleton origin.
   Separate support cases: both blocks nonzero, only first, only second,
   neither. Prove coverage and disjointness before counting.
4. **Sharp count.** A plane-containing partition has at most 2(q-1) disjoint
   residual lines, by an explicit skeleton hitting set. A no-plane partition
   has s=1 mod q singleton cells. Combine with the cyclic construction.
5. **Rigidity.** Classify skeleton intersections of every affine line. Use the
   exact incidence sum to locate the sole singleton at the origin. Then prove
   the 2x2 orientation classification. The q=3 equality cases remain outside
   this classification theorem.
6. **Full-map reduction.** Prove a nonzero hyperbola contains no affine line.
   Project each constant cell onto each nonzero-product block; the image is
   one point. Decompose into copies of C^k to prove the exact binomial identity.
7. **Scalar quadratic API.** Prove polarization, maximal isotropic dimension,
   split scalar count and defect. Prove the general bottleneck theorem using
   a maximal isotropic subspace and a constructive hyperbolic decomposition.
8. **Asymptotic rates.** Prove the elementary submultiplicative root-limit lemma,
   then the binomial-transform limit. No external conjectural bound is needed.

## Conditions for a later Gowers-localization application

A theorem transporting the finite-field construction must supply appropriate
minimum cell length or dimension, ambient containment, discarded-mass control,
and span/properness certificates. Exact cell-count savings alone do not imply
these properties. In the current full rank-one map, nonzero-product points
force singleton cells, so direct substitution into a positive minimum-length
interface is impossible.

## Verification acceptance criteria

A future `Lean-verified` status should require compilation in a pinned Lean and
Mathlib environment, inspection of exact theorem types, and a transitive axiom
audit. Successful numeric regression tests, a file with the right theorem name,
or a proof of a conditional/restricted replacement is not the same claim.
