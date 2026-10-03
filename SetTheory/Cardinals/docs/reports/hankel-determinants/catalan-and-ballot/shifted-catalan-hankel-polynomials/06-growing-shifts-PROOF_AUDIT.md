# Proof audit and trust boundary

This note records the delicate steps checked while preparing the article. It is
not an independent peer review or a machine-checked formalization.

## Definitions that must not be interchanged

The determinant size is N, not its final row index. N >= 1 and m >= 0 are integers.
The original perturbation is a = tau / mu, with

    v = m + 1/2,
    B = N + m + 1,
    c = v / (N B),
    mu = N B / (4 v).

The normalized determinant is R(tau) = D_N^(m)(tau/mu,1) / H_N^(m+1).
Its linear coefficient is exactly 1. Its concentration parameter is

    beta = [1 + c(v + 3/2)] / (v + 1) = sum_j w_j^2,
    theta_Nm = 1 / [(v + 1) beta].

The weights w_j are positive inverse Jacobi zeros normalized to sum to 1.
The limiting measure is **size-biased**, sum_j w_j delta_(w_j/beta), not the
unweighted empirical measure. The shape theta_Nm is finite-parameter; theta
without indices denotes its limit when such a limit is assumed.

## Exact algebra

1. The Catalan moment integral gives the weight x^(m-1/2)(4-x)^(1/2).
   Transforming by y = 1 - x/2 therefore gives Jacobi parameters m - 1/2, 1/2.
   The hypergeometric argument is -a/4, and becomes -c*tau after normalization.
2. The Christoffel quotient is (-1)^N H_N^(m) p_N^(m)(-a).
   Dividing by its value at a = 0 removes every monic normalization constant.
3. The transformed differential equation is

       tau(1+c tau) R'' + [v+(v+3/2)c tau] R' - v R = 0.

4. The inverse-moment recurrence includes a **negative** convolution term:

       (v+k) S_(k+1) = sum_{i=1}^k S_i S_(k+1-i)
          + c(k+v+1/2) S_k - c sum_{i=1}^{k-1} S_i S_(k-i).

   Omitting this term gives the wrong limiting law. The k = 1 identity yields
   the exact beta; k = 2 gives the exact cubic moment.
5. Exact rational comparisons between series division and this recurrence
   passed for 420 parameter pairs through moment 12. This tests the algebra
   independently of numerical zeros but does not prove all parameter values.

## Uniform bound and spectral limit

The proof of W <= 8 beta uses positivity to discard the negative convolution,
then a Catalan induction. It is valid also at m = 0. The factor 8 is not claimed
sharp. Its crucial role is W = O(beta), stronger than W <= sqrt(beta).
The latter weaker bound would not justify the stated Gaussian critical limit.

The recurrence for D_r = S_r / beta^(r-1) has limits because

    1/(v beta) -> theta,       c/beta -> 1 - theta.

Both endpoint cases theta = 0 and 1 are included. Uniform support in [0,8]
then promotes convergence of all fixed moments to weak convergence. The limiting
moment generating series is

    M(z) = 1/[1-(1-theta)z] + theta z M(z)^2.

Its branch with constant coefficient 1 equals the moment series of
1 - theta + theta Y, where Y has the Catalan density on (0,4).
No convergence of extreme zero locations follows from this argument; a
small-mass outlier is not excluded merely by the weak limit. Section 15 keeps
that sharper problem separate.

## Critical logarithmic scales

For tau >= 0 the scalar logarithm inequalities are global, so the displayed
finite bounds do not assume a small perturbation. Complex Taylor estimates
instead require |z|W < 1, ensured by 8 beta |z| < 1. The logarithm is the branch
vanishing at zero on this zero-free disk.

On the qth scale z = u beta^(-(q-1)/q), fixed q >= 2, the logarithmic tail after
order q is O(beta^(1/q)) on compact u sets. The subtracted lower moments must be
**exact finite-parameter moments**. Replacing them by limits without a convergence
rate could change or destroy the result because lower terms diverge on that
scale. No uniform assertion for q growing with N,m is made.

Sharpness on the positive ray follows from the critical limit and monotonicity
of exp(-tau) R(tau). It is not inferred merely from the sufficient error bound.
The if-and-only-if invisibility result is even simpler and holds for arbitrary
N,m sequences because 1+tau <= R(tau) <= exp(tau).

## Full nonlinear scale

The exact identity

    beta log R(t/beta) = integral log(1+t x)/x d nu_Nm(x)

has a removable singularity at x = 0. The integrand and each fixed t derivative
are continuous and uniformly bounded on x in [0,8], t in a nonnegative compact
interval. These are the hypotheses needed to pass to the limit uniformly,
including derivatives. The explicit algebraic branch is positive and regular
for all finite t >= 0. No positive-axis singular phase transition is asserted.

The nonlinear central limit theorem is centered at the exact mean. Weak
spectral convergence by itself is not accurate enough to replace this mean by
its first-order limit divided by beta on the square-root fluctuation scale.

## Poisson transition

The Bernoulli parameters are p_j = tau w_j/(1+tau w_j). Their mean lambda differs
from tau by

    delta = tau^2 sum_j w_j^2/(1+tau w_j).

The Barbour–Hall inequality is a credited external classical input. Under
beta*tau -> 0 it gives vanishing total variation to Poisson(lambda), while

delta/sqrt(tau) is asymptotic to beta*tau^(3/2).

The claimed second transition is only the comparison with the **nominal**
Poisson(tau). It does not say every Poisson approximation fails at beta^(-2/3).
The exact transition profile is proved using the single crossing of two
Poisson likelihood ratios; for an infinite normalized mean displacement,
Chebyshev separation suffices. The convention is d_TV = half the l1 distance.
The case of a vanishing scale parameter includes bounded tau and follows
directly from the quantitative bound.

## Proportional-growth prefactor

The finite parameters r = (m+1/2)/N and b = (N+m+1)/N satisfy
b = 1+r+1/(2N). Replacing b by 1+r before exponentiation can change the leading
constant; the theorem does not make that replacement.

The exponent is strictly concave, its unique saddle stays in a fixed interior
interval for positive compact ranges of m/N and t, and its curvature is bounded
above and below there. The factorial and rising-factorial square-root terms
are all retained. Endpoint rough Stirling bounds control the tails; a local
Gaussian lattice expansion supplies the prefactor. The odd N^(-1/2) corrections
integrate to zero, and the shifted Gaussian lattice sums have exponentially
small integral errors. This gives a relative O(1/N) remainder uniformly on the
stated compact parameter sets, not at their zero or infinite boundaries.

## Finite computational audit

All assertions in the delivered execution passed:

- 270 direct rational determinant comparisons;
- 420 rational parameter-pair moment comparisons through moment 12,
  comprising 5,040 moment equalities;
- 5,040 exact Catalan-majorant checks on those same parameter pairs;
- 60 exact limiting-recurrence checks;
- 16 floating-point Jacobi-root parameter pairs.

The driver additionally generated 5 critical-scale rows, 25 spectral-moment rows,
12 nonlinear-profile rows, and 36 prefactor rows. These tables are numerical
diagnostics, not outward-rounded interval certificates. Counts describing parts
of the same parameter grid must not be summed as independent parameter samples.

## What is not established

There is no claim of worldwide first discovery, peer review, Lean/Rocq checking,
or exhaustive inspection of the repository and literature. The work concerns
one additional linear factor, not all growing-degree multipliers. The exact
positive-axis statements do not transfer unchanged across negative zeros.
The limiting spectral law does not prove an extreme-zero theorem. The
fixed-order hierarchy does not settle growing-order uniformity. These are
explicit boundaries of the results, not hidden assumptions in their proofs.
