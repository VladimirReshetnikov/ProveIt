# Proof audit and dependency notes

This is an internal mathematical audit accompanying the manuscript. It is not
an independent review, formal verification, or proof-assistant certificate.

## 1. Constructing the analytic target before interpolating

Agreement with integer towers does not, by itself, prove the interpolation
series converges or satisfies the functional equation. The manuscript first
constructs the Koenigs coordinate Phi for g(u)=1-exp(-q*u), its positive inverse
H, and the normalized analytic function T(z)=exp(q)*(1-H(C*q^z)). Only then is
the finite q-binomial expression identified with its Newton interpolants.

## 2. The exact radius is a complex-disk statement

Real-axis analytic continuation is not enough to identify the Taylor radius.
Strictly positive coefficients give |H(q*s)| <= H(q*|s|). If the radius were
smaller than R=Phi(1)/q, the logarithmic equation would then extend H to a
strictly larger disk. The blow-up H(s)->infinity as s approaches R from the
left gives the opposite inequality.

## 3. Other same-modulus singularities are excluded

Positivity alone need not imply a unique dominant singularity. Here equality
in the triangle inequality, using the nonzero linear and quadratic terms,
shows that 1-H(q*s) has only the zero s=R on |s|<=R. Its derivative there is
nonzero. Dividing out that simple zero gives a nonvanishing analytic factor
on a slightly larger disk. Its analytic logarithm proves an exponentially
small remainder in the coefficient asymptotics.

## 4. Interpolation convergence is proved, not inferred

A residue formula yields explicit bounds on each Newton term and on the
interpolation remainder. All interpolation nodes are inside the chosen
contour because its radius rho is greater than 1. Since q^(-2)>1, such contours
exist for every compact subset of the target disk.

## 5. Boundary convergence uses a sufficiently strong remainder

A leading equivalent proportional to omega^n/n alone would not be enough to
prove conditional convergence on the unit circle. The manuscript proves an
O(n^(-2)) remainder there. Its uniform version on compact annuli also identifies
the boundary sum with the analytic continuation. At omega=1 the leading
coefficient is exactly -1/log(a), and summing the remainder gives a finite
renormalized constant with an O(1/N) tail.

## 6. Geometric nodes and the meaning of absolute convergence

At w=q^j, the Newton basis terminates. Such nodes are explicitly excluded from
nonzero term and tail equivalents. The absolute-convergence theorem concerns
the outer series of finite inner sums. It is not a claim about arbitrary
rearrangement of the original triangular array.

## 7. Uniqueness does not rely on periodic-perturbation intuition

The first proof uses finite Laplace measures and determinacy of moments on
[0,1]. The second, stronger proof uses convexity of log(L-S(x)) on a tail,
integer asymptotics, and the Koenigs equation. It does not use the Bernstein
representation theorem. Real injectivity of exponentiation propagates tail
equality to the full interval (-2,infinity), without assuming that the rival
solution is analytic.

## 8. Numerical and algorithmic limitations

The exact rational checks test finite identities, not the infinite-series
theorems. The other checks are floating-point comparisons. The positive
quadratic recurrence avoids the severe alternating cancellation of the
original transform but does not eliminate truncation, conditioning, or
roundoff. Its O(M^2) operation count is not a bit-complexity estimate. No
uniform-in-q claim is made as q approaches 1.

## 9. Domain limitations

The real inverse T^(-1)(y) is defined for y<L. A fractional iterate obtained by
shifting this inverse coordinate exists whenever the shifted height remains
above -2. All nonnegative iteration times satisfy that condition. Neither
the critical q=1 case nor base-2 or base-e tetration is covered. The first
boundary is classified, but the complete multivalued continuation is not.
