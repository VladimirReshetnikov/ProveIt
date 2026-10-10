# Audit and result-status register

## Proved in this delivery

- Global normalized-radius sign for all real b>0 at leading outer index a=1.
- Strict unique Student-type smoothed modes for the stated concave Green
  densities; monotone scale motion under monotone normalized curvature.
- Exact inverse-coordinate description of the whole upper-half-plane
  imaginary-zero curve, and a circle cutoff at 1/r_b for b>=1 (2 for b=1).
- Every odd central moment of the harmonic Green law has the sign of b-1.
- An all-moment exponential-skew inequality and exact radial coefficients
  through rho^4.
- Opposite local curvature signs at b=2 and b=4, excluding a universal
  convexity claim and complete monotonicity for b=2.
- Two monotone sectors of Hurwitz-shifted inner orders.
- All-inner-order generating transport, parity-separated functional
  identities, four constant specializations, and integer-shift reductions.

These statements have ordinary analytic/algebraic proofs in the article.
They are not established by the numerical grid or by finite replay alone.

## Existing statements confirmed or re-proved

- The leading-index-one signed density and the uniqueness/simple-root
  mechanism already occur in the source manuscript. They are not claimed
  as new discoveries.
- The local coefficient K(1,b) agrees exactly with -2 times the third central
  moment of the constructed law. No error was found in that formula.
- The source Cartesian-motion theorem correctly distinguishes its coordinate
  from normalized radial motion. Our result is a different derivative sign.
- Strict-mode uniqueness uses the classical strong-unimodality mechanism;
  the additional reflected-curvature/scale/radial steps are explicit here.

## Proposed local corrections

1. Update the a=1 full-radius branch from open to proved after review of this
   article. Keep all other parameter and arithmetic claims separate.
2. In the transport proof in `05-real-positive-kernel.tex`, replace
   `with $q=n$` by `with $x=n$` and `boundedness of $h$` by
   `boundedness of $q$`. These are notation repairs. They are not asserted
   to be newly discovered and may already appear in an incoming correction
   register.

## Explicit nonclaims

- No proof of the complete higher-outer-order normalized-radius conjecture.
- No S6/S8 proof, independence proof, or finite-weight minimal-depth claim.
- No circle-count theorem outside the unit disk for 0<b<1.
- No inference of universal radial convexity or complete monotonicity.
- No use of Cauchy-kernel log-concavity (it is not globally log-concave).
- No proof-assistant formalization or independent peer review.
- No exhaustive audit of the 379-page book or the incoming ZIP contents.
- No global-priority claim for the theorems or identities.

## Why the main extension does not automatically handle a>=2

The natural integrated signed density has second derivative
Q_(a,b)''(u)=kappa_(a-1,b)(u)/u, which changes sign. The strict concavity
hypothesis used in this delivery is therefore absent. This identifies a
specific missing hypothesis, not a reason to abandon the higher-index
problem.
