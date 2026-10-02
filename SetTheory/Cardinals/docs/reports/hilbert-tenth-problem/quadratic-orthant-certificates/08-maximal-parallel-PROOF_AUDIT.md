# Proof and scope audit

This is an audit of the supplied arguments, not an independent referee report.
No Lean or Rocq execution is claimed.

## Core certificate

Domain: every free and existential arithmetic coordinate is a natural number,
including zero. Positivity means nonnegativity on the *entire real nonnegative
orthant*, not nonnegativity on all signed real inputs.

Each reaction consumes a nonzero multiset. Reaction labels remain distinct.
The consumed reactants satisfy A f <= x; products cannot be reused in the same
round. Maximal means no coordinatewise extension, not maximum cardinality.

The comparator uses two affine squares and two nonnegative products. b+c=1
makes the flags Boolean over naturals. Complementarity kills the inactive
slack. The witness is unique at each threshold. The maximum-rule slack is
then uniquely determined. Sharing equal (species, threshold) comparisons
does not introduce a new choice.

With both x and y supplied, witnesses number d + 2m + 4H. The firing vector
is INCLUDED in this count. The other coordinates are unique given f, not
necessarily unique given x and y. The history count includes all new states.
First halting forbids zero extents before the terminal state and checks the
last state's reactants directly. At a deadlock, the base semantics has one
zero-extent stutter. Horizon zero is handled explicitly.

## Variants

Pre-state guard bits are computed from x, never from the residual or output.
Disabled rules have f_j=0. Flat maximality tests only rules that are both
eligible and unused. Retention changes y=D r+B f, not the maximality test.
Fixed membrane topology is a species-indexing reduction only when its exact
operational rules agree with these definitions. Dynamic membrane creation
or dissolution is not claimed covered.

## Counting

For each maximal extent, select one deficient species per rule. The union
is a cover J and its residual values are bounded by the largest consumption
coefficient. For each fixed bounded residual vector, fixing m-rank(A_J)
coordinates determines all remaining extent coordinates at most once. This
proves the uniform upper bound.

For sharpness at EVERY matrix, choose a rank-minimizing cover J, set
v=A*1+1_(J-complement), and perturb n*1 by small integral combinations of a
basis of ker(A_J). Residuals are zero on J and remain nonnegative outside;
all extents remain nonnegative. The parameter box has dimension m-rho(A).
Thus the exponent is attained along this integral ray, not just conjectured
from examples.

Fixed-horizon trace counts are finite Presburger fibers. Eventual
quasipolynomiality uses Woods's theorem. The degree bound uses the new rank
estimate and a separate population-mass estimate. The bound is not asserted
for arbitrary guards using the full unguarded matrix. Flat eventual
constancy excludes modular guards and tests.

The counting-hardness construction maps independent sets to maximal independent
sets via private leaves, then to resource-sharing vertex reactions. The map
is parsimonious; #P completeness is under polynomial-time Turing reductions,
not parsimonious completeness from arbitrary #P functions. Rule arity is not
bounded in this reduction.

## Convexity and degree

A convex rational quadratic with a rational orthant zero has a rational
polyhedral orthant zero set. If an existential projection covered both
integer coordinate axes, rational recession rays from the two axis slices
would combine into a natural zero with both coordinates positive. Hence
finite-dimensional convex lifting does not solve the cooperative deadlock
example. This is a global, unbounded-population obstruction.

The degree-at-most-three semilinearity lemma is inherited from the repository,
with a self-contained proof repeated in the article. It relies on global
orthant nonnegativity. On each face containing a natural zero, the relative
interior zero set equals a rational affine subspace intersected with that
face. Finite unions and natural projections are Presburger.

Numerical parameter uniformity makes resource balance bilinear; squares
therefore produce quartics. The lower bound specializes to A -> kB, whose
maximal output is z=kn. A low-degree positive representation would make the
squares eventually periodic. This proves a threshold only in the stated
positivity class, not an unrestricted cubic Diophantine impossibility.

## What is not concluded

- No verified global priority claim or resolution of a named published conjecture.
- No new minimal universal rule count.
- No fixed-arity single-fold or finite-fold representation for unbounded halting.
- No general polynomial-time root-counting or resource-cover optimization algorithm.
- No transfer of proof-assistant status from repository MRDP code to these theorems.
- No claim that finite tests prove the universal theorems.
