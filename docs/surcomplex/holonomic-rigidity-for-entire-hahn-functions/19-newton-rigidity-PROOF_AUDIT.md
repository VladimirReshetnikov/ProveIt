# Internal proof audit and verification boundary

This is an internal audit of the written argument, not an independent referee
report or proof-assistant certificate. The article is authoritative for statements
and proofs. No Lean proof of the new results is included or claimed.

## Assumptions that must remain explicit

- K = k((t^Gamma)); k is characteristic zero and trivially valued.
- Gamma is nonzero, ordered, abelian, and set-sized. No divisibility, rank-one,
  order-unit, algebraic-closedness or countable-cofinality assumption is needed.
- The function variable is an ordinary formal variable; the derivative kills K.
- Strong summability is tested on the coefficient evaluation family before
  cancellation. It is not ordinary complex convergence or a surreal fine limit.
- Entireness is relative to ONE fixed Hahn workspace.
- External constant extensions affect polynomial relations, not the analytic domain.

## Main dependency chain

1. **All-scale criterion.** Necessity uses strong summability at two scales:
   a hypothetical infinite bounded sequence at delta becomes a descending sequence
   at delta+epsilon. Sufficiency uses finite support participation below each bound.
   This criterion is background already recorded in the repository, not a novelty claim.
2. **Divisible hull.** The original ordered group is cofinal in its divisible hull.
   The all-scale criterion proves preservation of entireness for this specific
   extension. It does not justify arbitrary noncofinal scalar extension.
3. **Initial polynomial.** Normalized coefficients have nonnegative valuation,
   and cofinal coefficient values make the zero-valuation layer finite. Reduction
   is a nonzero polynomial. Its Gauss minimum is not the value of the function at
   the single scalar t^(-delta), which can cancel.
4. **Escape.** A single nonzero coefficient beyond a prescribed degree defeats
   every smaller coefficient at sufficiently exterior scales. BOTH the minimum
   and maximum active degrees then exceed the prescribed bound.
5. **Attained transition.** One candidate crossing slope gives an upper window R.
   Cofinal coefficient values make the candidate slopes <=R finite. Their minimum
   is therefore attained. There is no use of an infimum of an arbitrary subset of
   a non-complete ordered group, and no assumed cofinal sequence of scales.
6. **Exterior corner.** Euler conversion is invertible over K(z) and preserves
   differential-degree bounds. A finite highest-degree, highest-z-weight corner
   survives reduction. Lower-degree terms are excluded using a high nonzero
   coefficient of the solution and the sign-sensitive inequality below.
7. **Second order.** The homogeneous monomial-jet kernel is the principal conic
   ideal (Y0*Y2-Y1^2). Removing its maximal power gives a nonzero one-variable
   polynomial in the monomial degree. Outside finitely many degree exceptions,
   any residue solution must be a monomial, contradicting the transition.
8. **Third order.** The first polar is divisible by (U-T)^2. Its remaining factor
   has U-degree <=1. The bottom and top mixed coefficients force integer roots
   on opposite sides, while a Q-linear projection proves a common eventual side.
   A nonzero homogeneous form of POSITIVE degree <=3 cannot have all first
   partials vanish on the twisted cubic: each secant restriction would have two
   double zeros, and the secant map is dominant.
9. **External constants.** A K-linear functional on the finite span of relation
   coefficients extracts a nonzero relation over K, preserving degree. This is
   coefficientwise formal algebra, not an infinite linear or analytic operation.
10. **Planar systems.** The derivatives lie in a finite algebraic extension of
    L(z,f,g). Minimal-polynomial separants are nonzero in characteristic zero.
    Differentiation puts second derivatives into the same extension; transcendence
    degree <=2 then produces a relation among f,f',f'' and likewise for g.

## Critical inequality in the exterior reduction

A normalized coefficient has valuation

`v(c)-mu + (d-D)*gamma_delta - (w-W)*delta`.

For `d<D`, the bound `gamma_delta <= alpha_N-N*delta` is multiplied by the
NEGATIVE integer `d-D`, so the inequality reverses. The resulting lower bound is

`v(c)-mu-(D-d)*alpha_N + ((D-d)*N-(w-W))*delta`.

Choose one ordinary index N making every final integer coefficient positive,
then one scale dominating the finitely many constant terms. No Archimedean
comparison or division by a value-group element is involved.

## Higher-order exact examples

- The quartic H3 has identically zero first polar, so the basic criterion fails.
  The resultant identity introduces a common-root parameter N. Differentiation
  produces `(4*f*N-3*E(f))*E(N)=0`. The branch with the first factor zero must
  be handled, not divided away. It reduces to `8*E(U)-U^2=0` for U=E(f)/f,
  which has no nonzero formal solution with zero constant term.
- In the fourth-order quadratic Q4, the pair symbol is
  `(m-n)^2*(m-2*n)*(n-2*m)`. The first two support degrees must be m,2m.
  A first later term cannot cancel its cross contribution with the mth term.
- All formal solutions of either equation are zero, monomials, and the specified
  doubling binomials. These are not counterexamples to polynomial rigidity.
- The sparse strongly entire series with degrees 2^j and valuations 4^j has
  initial polynomials solving both equations at every scale, but Q4 has the
  explicit nonzero coefficient `-126*t^17` at z^5. Initial vanishing is not
  enough to conclude that an actual equation is satisfied.

## Explicit limitations

The manuscript does not resolve unrestricted all-order rigidity with an order
unit, does not prove the meromorphic order-unit analogue, and does not claim
all-order differential independence from three-jet independence. It does not
make a point-value independence claim or solve omnific factorization problems.
The omnific consequence concerns finitely many coefficients of formal relations.

The finite verification run passed 259 exact assertions. Infinite-support,
cofinality, arbitrary-field and novelty assertions are not inferred from tests.
A complete source-repository build and independent Lean verification were not run.
