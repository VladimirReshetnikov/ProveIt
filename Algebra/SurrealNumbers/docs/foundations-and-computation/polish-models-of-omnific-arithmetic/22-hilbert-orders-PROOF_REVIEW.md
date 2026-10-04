# Internal proof review

Date: 4 October 2026.

This is an internal, AI-assisted argument review, not an independent referee
report, formal proof certificate, or priority assessment. The following records
what was checked and which inputs remain classical dependencies.

## 1. Additive cone to halfspace

The initial hypothesis is only translation-invariant additive total order;
compatibility with positive real scalars is not assumed. Positive rational
homogeneity follows from divisibility and trichotomy.

Baire category makes the cone nonmeager. On an open set U where it is comeager,
the two comeager sets P and z-P meet for every z in U+U. This establishes an
actual open subset of P, rather than merely an open subset of P-P.

The closure of P is a real convex cone by rational approximation. The negative
of the interior of P is open and disjoint from that closure, so the closure is
proper. Separation therefore applies. Totality makes the closed cone exactly
a continuous closed halfspace, not merely a subset of one.

Appendix A checks separation without assuming local convexity. The gauge is
finite because the open convex set contains zero and is absorbing. The
Hahn--Banach extension is continuous because it is bounded on the intersection
of that neighborhood with its negative. This is enough for the L^p application.

## 2. Transfinite recursion and termination

Borel traces on closed linear subspaces remain Borel. Merely having the Baire
property in the original ambient space is insufficient; the article supplies
a counterexample with an irregular order on a meager hyperplane.

At each nonzero stage the next boundary is a closed real hyperplane. At limit
stages the intersection is used; no sequential-basis argument silently replaces
an ordinal by omega.

If every countable stage remained nonzero, each strict successor step would
supply a distinct element of a fixed countable topological base: it meets the
old subspace and misses the new one. A later subspace cannot meet that same
open set. This is the countability contradiction establishing termination.

A nonzero vector first leaves at a successor, not at a limit. This justifies
the union of oriented layers, real scalar compatibility, and the countable
F_sigma description. The reflected cone plus zero supplies the complementary
F_sigma description.

## 3. Hilbert basis and algebraic rank

The orthogonal direction at a codimension-one step is unique once its norm and
orientation are fixed. Intersections at limits recover orthogonal complements
of the closed span of earlier directions. Termination at zero proves
completeness of the resulting orthonormal family.

Archimedean comparison uses integer multiples and is invariant under arbitrary
additive order embeddings; neither Borelness nor real linearity is needed for
this necessity argument. The set of leading ranks is the ordinal itself.
Every nonzero convex subgroup has a least leading rank and contains the whole
tail at that rank by integer domination. This excludes hidden nonclosed convex
subgroups and proves the complete tail classification.

The zero space has index 0. Finite Hilbert dimension n has index n. Infinite
separable Hilbert dimension permits every countably infinite ordinal, including
omega+1 and omega^2. These are not mere re-enumerations preserving the given
well-order. The examples explicitly exhibit the difference.

## 4. Oscillation rank

The derivative is explicitly defined using oscillation at least epsilon.
For a characteristic function and 0 < epsilon <= 1, it is the relative boundary
inside each closed stage. Perturbations x +/- t u at a kernel point give both
values, and points outside the kernel have a neighborhood of constant sign.
The iterates agree with the flag through its terminal singleton. One further
derivative is required to reach the empty set. Thus the rank is theta+1, not
theta. The zero-space case gives rank 1 and obeys the same convention.

Homeomorphisms of ambient pairs preserve all derivative stages. Equality of
successor ordinals implies equality of the indices. This statement concerns
the ambient pair, not the positive cone considered as a bare topological space.

The Baire-class-1 approximation uses disjoint closed approximants of the cone
and its complement. Distances cannot vanish simultaneously at one point because
the sets are closed and disjoint. Empty stages are handled by constant functions.

## 5. Operators and closed images

Automatic continuity applies to Borel additive maps, with a category argument
included. Real linearity follows from continuity and rational approximation.
For the pivot criterion, boundedness is a hypothesis, not a consequence of a
formal matrix condition. Unconditional Hilbert sums and continuous coordinate
evaluation justify passing from columns to vectors with infinite support.

Strictly increasing pivot ranks and positive pivot entries are necessary and
sufficient for a bounded operator to be an order embedding. For automorphisms,
bounded invertibility is separately required. The shift, the decaying diagonal,
and I+cS distinguish isometric embedding, nonclosed image, and automorphism.
A discontinuous additive shear prevents an overstatement that every algebraic
order isomorphism is Borel.

A Polish subgroup is G_delta and comeager in its closure, so it equals its
closure. This verifies the inherited-topology closed-image criterion.

## 6. Arithmetic

Division with remainder is explicit for every positive standard integer m:
(x,n) = m(x/m,q)+(0,r), with n=mq+r and 0<=r<m. Nonnegative inputs have
nonnegative quotients even when the integer coordinate is negative, because
a positive Hilbert coordinate dominates all integer coordinates.

The full Presburger conclusion and elementarity rely on the classical
Z-group characterization and quantifier elimination with congruence predicates.
These are identified as standard inputs, not computationally verified here.
The claim about all definable relations being Delta^0_2 follows by that
elimination and finite Boolean closure. Congruence is controlled only by the
integer coordinate.

An injective unital monoid map extends to the group completion and reflects
order. The subgroup divisible by every standard integer is exactly H x {0};
its preservation and preservation of the unit force the claimed map form.
For Borel maps, positive/negative parts provide a Borel group extension.

The Polish-image proof uses the finite union of the image cone and its negative,
which is the group image. A finite union of G_delta sets is G_delta, so the
Polish-subgroup argument applies. No implication from abstract Polishability
to inherited Polish topology is used.

The minor zero-index edge case in the component statement was checked: the
article says every *nonempty* integer slice is a connected component.

## 7. Omnific interpretation and topology

The exponents theta-alpha use surreal subtraction, explicitly not ordinal
subtraction. They are strictly decreasing positive surreal numbers, and every
subset of the index ordinal gives reverse-well-ordered exponent support.
The classical surreal normal-form theorem is the only substantive surreal
input; addition and sign comparison on the fixed supports are coefficientwise.

Square-summability restricts coefficients, not the allowable support subsets:
weights 2^(-b(alpha)-1) realize every subset. All images under discussion are
sets; no topology or quantification over a set of all surreal numbers is used.

The transported Hilbert-product topology is Polish. In contrast, the
coefficient-product topology gives a proper dense l^2 subgroup, which is not
Polish in that topology; the inherited surreal order topology is discrete.
None of these different topologies is silently substituted for another.

## 8. Ring obstruction

The divisible subgroup is an ideal under any proposed ring multiplication,
by divisibility under each standard integer. It has an additive order unit u
such that every one of its elements is below some n u. In an ordered ring,
u is above all integers, so u^2 > n u for every positive n, while u^2 belongs
to the same divisible ideal. This is the contradiction. It uses neither
measurability nor commutativity of multiplication. The case theta=0 is excluded.

## 9. Computation, literature, and limits

The 136,562 exact finite assertions cover elementary sign, pivot, inverse,
remainder, fixed-support addition, and explicit perturbation instances. No test
checks a transfinite theorem or infinite-dimensional completeness.

No major mathematical defect was found in this internal review. This does not
replace independent expert review or formal verification. Most importantly,
priority of the converse classification cannot be certified without a full
comparison with earlier total-order cone literature; the unavailable 2012
paper is an explicit source-audit limitation rather than an ignored source.
