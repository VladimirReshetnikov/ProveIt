# Proof dependency map and formalization roadmap

No Lean source is included and no formal verification was performed. This file
is a proposed sequence of independently reviewable proof obligations.

## Dependency map

| Result | Inputs |
|---|---|
| Coefficient enclosure | finite l3-l2 inequality, strict monotonicity |
| Endpoint chord | enclosure, probability weights c_i^2, third-sum identity |
| Fourth defect | finite sum algebra, enclosure |
| Main comparison | chord, finite Poisson differentiation, exponential uniform integrability |
| Equality p>3 | strict power convexity in the exact deficit identity |
| Equality p=3 | full support of the interior Gamma-difference interpolant |
| Kurtosis frontier | fourth defect and cumulants |
| Moment stability | deficit identity, scalar convexity bounds, variance-two localization |
| Spectral rigidity | actual coefficient interval, bilinear corner inequalities |
| Laplace bound | convex normalized exponential remainder |
| Tail scale | feasible two-mode law and Gaussian tail asymptotic |
| Infinite-mode comparison | finite comparison, L2 convergence, exponential uniform integrability |

## Stage 1: finite real algebra

Formalize a finite coefficient vector, squared sum one, cubic sum delta, and
nonnegative endpoint parameters a,b with a^2+b^2=1 and a^3-b^3=delta. Avoid
trigonometric parameterization initially: uniqueness/existence can be isolated.

Prove the remaining-coordinate l3-l2 inequality and monotonicity of
x^3-(1-x^2)^(3/2) on [0,1]. Derive -b <= c_i <= a. Then prove

    (delta+b)/(a+b) = a^2
    (a-delta)/(a+b) = b^2
    a^4+b^4 - sum_i c_i^4 = sum_i c_i^2 (a-c_i)(c_i+b).

The exact test script records the algebraic identities, but does not certify
these universal analytic inequalities.

## Stage 2: the finite weighted chord

For each convex phi on [-b,a], prove the chord inequality and integrate it over
the finite probability measure sum_i c_i^2 delta_(c_i). Formalize the strictness
criterion separately, so zero coefficients cannot spuriously force equality.

Prove the spectral-distance formula only after defining zero padding explicitly.
The bilinear corner check and the zero-skewness sharpness sequence are finite
real algebra once the distance formula is established.

## Stage 3: probability distributions and cumulants

Construct independent standard Gaussians and centered quadratic sums on a
finite product measure. Establish the MGF and its first four derivatives or
moments directly. The OpenAI repository file cited in the manuscript supplies
inspiration for mean/variance organization; its existence is not a certificate
for this new theorem.

The exact fourth-moment frontier can be formalized at this stage without
formalizing the full interpolation comparison.

## Stage 4: finite compound-Poisson differentiation

Define the truncated pushforward measures and centered compound-Poisson laws.
Prove the intensity derivative from the finite-measure Poisson series, including
the derivative of centering. Combine with Taylor's integral remainder. Ensure
that the derivative is justified for the signed difference of endpoint measures
while the interpolated intensity stays positive.

First prove the identity for compactly supported C^2 tests. Use cutoffs only to
obtain an identity; the cutoffs need not preserve convexity. Recover the convex
function before concluding nonnegativity.

## Stage 5: convergence and equality

Formalize the uniform bound E exp(|X_(u,epsilon)|/4) <= 2 exp(1/8), weak
convergence of the truncated laws, and uniform-integrability transfer for
polynomial-growth observables. The integrated deficit identity needs domination
uniform in the interpolation parameter as well as the truncation.

For p=3, strict convexity is unavailable. Formalize the full-support argument
for the difference of two positive-shape Gamma variables, and the positive
probability of the chord endpoints straddling zero.

## Stage 6: quantitative and extended results

Formalize the scalar power-gap inequalities and the restricted-event proof for
3<p<4. Keep exact p=4 coefficient 48 separate from the weaker general formula.
Then treat the Laplace envelope directly rather than inserting an exponential
into the polynomial-growth theorem. The Gamma and infinitely divisible
extensions should each carry their own assumptions, without importing a false
strictness assertion for a Gaussian base.

## Certification boundary

A Lean file which assumes the main comparison and checks only its algebraic
consequences would certify only those conditional consequences. It must not be
reported as a formalization of Theorem 2.1. Likewise, replacing weak convergence
or uniform integrability with an axiom would leave the central analytic step
uncertified. The roadmap is intended to keep those boundaries explicit.
