# Further reductions suggested by the direct-system construction

The present result changes the source coding while retaining the inherited
ten-integer Lucas bridge. It does not establish an absolute minimum in
unknowns, degree, coefficients, or operations. The following projects have
precise mathematical validation conditions; none is counted as an additional
achieved reduction in this release.

## 1. Use the actual monomial supports

The delivered 32-position Sidon list separates every possible quadratic
monomial in 31 variables, including the constant and linear terms through
zero padding. Most such monomials do not occur in the 22 source residuals.
It may be possible to use a shorter list when only the necessary target
extractions are protected.

Let T be all multi-indices of degree at most two, let S_k be the support of
residual r_k, and write e(alpha)=sum_i alpha_i a_i. For proposed positions
a_i and target exponents t_j, require the following finite certificate:

    t_k-e(alpha)+e(beta)=t_j
        if and only if k=j and alpha=beta,

for every k,j, alpha in S_k, and beta in T. This condition gives exactly the
desired coefficient 2r_j at target t_j. Collisions away from those targets
are harmless. It also permits some collisions between absent monomials,
so a global Sidon property is sufficient but potentially stronger than
necessary.

A search can optimize the positions and target exponents jointly, using
integer programming, SAT, or direct finite search. A delivered answer
should include the resulting integer lists and an independent exhaustive
checker for the displayed condition, not only a search log.

## 2. Pack marked targets more closely

The current uniform spacing 2M+1 gives a short proof because every other
block misses a marked centre. The condition in Section 1 allows nonuniform
spacing based on the actual source supports and may reduce the maximum
exponent further. Reordering residuals and permuting the assigned input
positions are available finite choices.

Two additional obligations must be rechecked after such packing. All
reversed exponents t_k-e(alpha) must be nonnegative. If reversed source
blocks overlap, the coefficient bound must use the aggregated coefficients
of D, rather than the previous maximum single residual coefficient A.
The highest nonzero coefficient of D must remain strictly positive to
establish D>0 before decoding g. It is unsafe simply to retain the old
base bound after removing the disjoint-block hypothesis.

The objective should include both the final polynomial degree and its
literal circuit length. A shorter exponent span need not produce the
shortest shared-power evaluator.

## 3. Simplify the parent system and source circuit

The current bridge starts with 31 positive parent coordinates and 22
quadratic residuals. An exact elimination of a coordinate or a residual
could improve several downstream parameters at once. Such an elimination
must preserve positive integer existence in both directions. A linear
substitution that produces rational coordinates or destroys positivity
does not suffice.

There are also purely algebraic opportunities: factor common coefficient
recipes, share powers between reversed blocks, and search better addition
chains for the fixed exponents. These changes should be proved as exact
polynomial identities when the polynomial is unchanged. If only zero-set
equivalence is asserted, the additional arithmetic hypotheses belong in
the proof. All binary additions, subtractions, and multiplications by
numerals should remain charged under the current comparison convention.

## 4. A simultaneous residual construction in general degree

The same proof extends to fixed degree delta>=1. For a system of m
integer polynomials of degree at most delta in n nonnegative variables,
choose positions 0=a_0<a_1<...<a_n=M whose unordered delta-fold sums
are distinct, with repetition allowed. Padding with a_0 handles all
lower-degree monomials. Define

    c_(j,alpha)=(delta-|alpha|)! product_i(alpha_i!) [x^alpha]r_j,
    stride=delta M+1,
    t_j=delta M+(j-1)stride,
    Q=(m+1)delta M+m-1,
    D=sum_(j,alpha)c_(j,alpha) B^(t_j-e(alpha)),
    B=beta b^delta,
    J=2(1+g)^delta D+sum_(i=0)^Q B^(i+1).

The coefficient at target t_j is delta! r_j. As in the quadratic proof,
the reversed blocks are disjoint and other product blocks miss each
marked target. If A is the largest absolute weighted coefficient, the
explicit sufficient base bound

    beta > max(4(n+1)^delta A, 4*3^delta A)

gives both the carry bound and the arbitrary-g size bound. Place a
residual with positive constant term last; the source system must omit
the origin for the same positive-interval completeness statement.
Choose beta as a sufficiently large square power of two, and use
b=4^t in completeness. Then B is a power of four, preserving 3|X.

Thus the source height is controlled by m, delta, and the diameter of an
additive set, rather than by a positional code exponential in the number
of variables. Classical additive constructions provide appropriate sets
for fixed delta; their use here is not a claim to have discovered those
constructions. A separate implementation should verify the finite set,
coefficient bounds, source normalization, and both existence implications
before substituting this general adapter into the inherited final bridge.

## 5. Formalization and evidence

The next strongest validation would formalize the source adapter as an
abstract theorem about a finite residual list and a finite additive-code
certificate. The proof separates naturally into coefficient extraction,
signed carry control, low-digit decoding, and the binomial valuation
identity. This avoids asking a proof assistant to expand the very large
final polynomial.

Such a certificate would strengthen only the newly changed source layer.
The inherited K215 compiler calibration and external Lucas/interpolation
results remain separate proof obligations. Any later release should state
which layers have actually been formalized and preserve their source and
coefficient identities.
