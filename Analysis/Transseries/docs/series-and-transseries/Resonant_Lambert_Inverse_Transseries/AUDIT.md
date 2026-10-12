# Scoped mathematical audit

## Finding

No new incorrect theorem was established in the inspected repository sources.
No corrective patch to a canonical manuscript is supplied. The audit is
substantive and limited: it does not cover the entire corpus or the contents of
all incoming ZIPs.

## Two safeguards for extending the existing material

### 1. Analytic-tail convergence is not preserved by the Lambert superposition

The selected prior Lerch/dilogarithm drafts explicitly assume or prove
holomorphic analytic tails. Those statements are not contradicted here. For the
new Lambert specialization, the even tail coefficients satisfy

    r_n = 4 Gamma(n) zeta(n)^2 / (n (4*pi^2)^n),  n even >= 2.

They have factorial growth. The inverse coefficient polynomials have alternating
coefficientwise signs; for positive fixed u their even coefficients have
absolute value at least u*r_n. Thus the ordinary inverse series has radius zero,
while its shifted Borel transform has exact radius 4*pi^2. A future integration
that applies an ordinary convergent analytic-tail theorem to this particular
Lambert tail would therefore be wrong. Article Theorem 7.2 supplies the correct
Gevrey statement instead.

### 2. Arithmetic averaging and functional inversion do not commute

The real forward function is the arithmetic average of its two exact forward
lateral functions. The arithmetic average of their inverse branches is NOT the
real inverse. With t the actual positive inverse and W=log(1/t)+EulerGamma,

    (g_plus + g_minus)/2 - g_0
      = -t^2/W^2 * exp(-8*pi^2/t) * (1+O(t)).

Article Theorem 8.2 proves this nonzero defect and fixes its leading coefficient.
It is a warning against an unsafe identification, not an allegation that any
inspected source made it. A nonlinear median summation operator is not generally
the plain arithmetic average of two nonlinear inverse branches.

## Normalizations checked

The source uses upper-minus-lower Borel discontinuity, so the base jump is
`+4*pi*i*sum d(n)*E1(4*pi^2*n/t)`. The Borel transform divides the t^k coefficient
by Gamma(k), not by k!. The second-order parity restoration applies only to the
odd-power projection of the order jet. The two different large X variables in
Sections 6 and 7 have distinct, explicitly stated target normalizations.

The displayed third inverse coefficient was reconciled against the exact
symbolic result during preparation; the final coefficient of u^3 is 7/288.
This was a transcription correction in the new article, not a repository error.
The lateral-root numerical diagnostic was changed from a generic secant solver
to explicitly differentiated Newton iteration with a final residual check.

## Not claimed

No global inverse Borel continuation theorem, no full-function complex fold
classification, no proof of the Section 11 large-order conjectures, no interval
certification, no Lean verification, and no exhaustive priority review.
