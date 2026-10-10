# Incoming correlation audit and new continuation

Pinned repository commit: `fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`.
All five current incoming archives were inspected as extracted files. The
new mathematics is in `sections/05-dilation.tex`; proofs do not assume that
unresolved period-independence questions have answers.

## Existing results that must receive prior credit

- `ProveIt_Stieltjes_Correlation_Closure/.../article.tex` proves the
  all-index linear Stieltjes closure for one circular translation,
  including `I00 = gamma1(a)+gamma1(1-a)-2*zeta(2)`, a missing-order
  rule, coincident finite parts, and log-Gamma correlations.
- `ProveIt_Shifted_Hurwitz_Jets/.../sections.tex`, lines 315–425,
  proves all-index undilated derivative contact corrections and reduces
  arbitrary undilated polygamma correlations to first Hurwitz derivatives.
- `ProveIt_Stieltjes_Convolution/.../article.tex`, sections 2–7,
  establishes the entire periodic distribution semigroup, one-generator
  convolution closure, all-index contact terms and arbitrary polygamma
  convolution formulas. Associativity of the convolution operation is
  therefore already supplied in the current incoming set.
- `Stieltjes_Convolution_Calculus/.../Stieltjes_Convolution_Calculus.tex`
  substantially overlaps this semigroup, finite-part, derivative and
  correlation calculus and also develops collision and Gamma material.
- `ProveIt_Resonance_Correlations/.../sections/03_gamma.tex` develops
  ordinary shifted Hurwitz and Gamma correlations and balanced negative
  polygamma correlations; these ordinary correlation mechanisms are
  antecedents, not new claims of the present contribution.

The Closure report's questions about parameter differentiation (lines
1256–1261) and associative convolution (1271–1277) are answered in other
archives in the supplied current set. They should be reconciled at
integration instead of presented as still-open questions globally.

## Explicit questions resolved here

1. Closure `article.tex` lines 1247–1254: unequal positive integer
   dilations and all additional endpoints.
2. Shifted Hurwitz `sections.tex` lines 782–783: exact commutators
   between dilation, canonical periodic extension and differentiation,
   including traces and subtraction-scale dependence.
3. Convolution Calculus `Stieltjes_Convolution_Calculus.tex` lines
   1705–1712: normalization under rescaling. We resolve linear positive
   integer coverings, not its separate nonlinear-coordinate question.

## New theorem package

- Exact finite-part pullback correction at arbitrary Stieltjes index and
  argument derivative order, with finite harmonic-number coefficient
  polynomial `c_{n,r}(L)`.
- Ambient-coordinate derivative commutator `b_{r,n}(L)` and exact
  compatibility with successive scales.
- All-order multiplication/trace formulas retaining the point masses
  and their derivatives.
- All-index Stieltjes product closure for unequal integer dilations,
  with explicit reduced shift and all logarithmic normalization terms.
- Every mixed argument derivative of that product.
- Especially short polygamma formula in which `log(lcm(p,q))` is the
  scale term, and an elementary separate base formula for digamma.
- An ordinary absolutely convergent integral realization displaying
  every local counterterm; this provides the independent numerical test.

These are new derivations relative to the inspected repository and five
incoming archives. No global literature-priority theorem is claimed.
The distributional Fourier mechanism is classical. The supplied papers
already cite Zhi-Hong Sun, *On the properties of invariant functions*,
arXiv:2209.14625 (2022), Remark 3.2, and classical Hurwitz Fourier theory.

## Scope and cautions

- No new false mathematical theorem was identified in the sampled
  incoming correlation formulas. The present work supplies an omitted
  scale theorem and reconciles stale questions, rather than inventing
  an erratum.
- `FP_x` is the Hadamard constant term with unscaled local coordinates
  `x-x0` and zero added finite point-supported terms. True distribution
  pullback is not the same convention. The theorem explicitly converts
  between them.
- The grids must be disjoint: if `d=gcd(p,q)`, this means
  `(p/d)*a` is not an integer. Colliding unequal grids are left open.
- Derivative symbols inside the integrand act on the special-function
  argument. They do not differentiate the discontinuous fractional-part
  map; the distribution theorem supplies the required local terms.
- The source statement that the undilated derivative anomaly vanishes
  at Stieltjes index `n >= r` is correct. At a nontrivial ambient scale it
  need no longer vanish: `D X_{q,n,0} = q X_{q,n,1} -
  (log q)^n Delta_q'/q`. This distinction should be explained in the
  integrated manuscript.

## Verification artifacts

- `code/check_dilated_polygamma.py`: independent subtracted-integrand
  quadrature, nine tests at 42 decimal digits, all passed. Maximum
  relative discrepancy less than `3.5e-39`.
- `results/dilated_polygamma.json`: observed numerical output. No certified
  interval error bound is claimed.
- `code/check_dilated_stieltjes.py`: independent subtracted-integrand
  quadrature at positive Stieltjes indices; results in adjacent JSON.
  All three cases `(m,n)=(1,0),(0,1),(1,1)` passed 28-digit checks;
  the largest relative discrepancy is below `9e-29`.

## External source check

Web review recovered official DLMF 25.13 and the original paper Roger
Gay and Ahmed Sebbar, *Pseudo-differential operators on the circle,
Bernoulli polynomials*, Quantum Studies: Mathematics and Foundations
11 (2024), 1–25, DOI `10.1007/s40509-024-00316-9`. They support the
classical spectral setting, not a claimed priority for the specific
all-index scale formula. No external-source quotation is needed.
