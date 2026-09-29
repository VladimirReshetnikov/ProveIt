# Proof status and scope

## Repository problem addressed

The consulted countable-feedback draft already had coefficient regularity and
a canonical left-sector Poincare realization. It explicitly did not prove
uniform Gevrey remainders or directional Borel summation. This article addresses
that stated boundary. It does not reuse the predecessor's unreviewed sharp
numerical-type identity or the neighboring finite-core saddle theorem as a
proof assumption.

## Results proved in the article

- Formal existence, uniqueness, the finite Lagrange coefficient formula, and
  the positive subfamily estimate linking kernel coefficients to solution
  coefficients.
- A fixed dependent-variable disk after the normalization U = q V, for
  arbitrary finite nonnegative slopes.
- An exact all-orders exponential Taylor-remainder estimate for the kernel.
- A weighted implicit remainder theorem under monotone quotient, root-quotient,
  and shift bounds stated explicitly in Section 2.
- Equivalence of formal coefficient regularity and strong sectorial regularity.
- The Gevrey coefficient and strong-remainder criterion, proved independently
  of the predecessor's sharper exact-type assertions.
- The optimal factorial-logarithmic weight under two-sided comparable
  power-logarithmic slope growth, and actual optimized upper error bounds.
- Formal weighted reversion, actual sectorial inverse existence, and strong
  inverse remainders.
- Finite-action and iteration analytic error bounds.

Standard tools include formal Lagrange inversion, Cauchy estimates,
Stirling's formula, contraction mapping, and analytic implicit inversion.
The text supplies the model-specific arguments and the weighted implicit proof.

## External theorem used for summability

The conversion from strong Gevrey or strongly regular asymptotics on a
sufficiently wide sector to directional summability uses the classical
sectorial characterization and generalized reconstruction theorem of
Lastra--Malek--Sanz. The article names its definitions/theorem and verifies
that the available opening exceeds the required critical opening when k > 1.
For generalized factorial-logarithmic summation, standard strong regularity
and opening-index facts are also cited to primary literature.

## Essential hypotheses

Slopes are finite nonnegative real numbers. Positivity is used for necessity
and coefficient comparisons; negative or complex slopes are not covered by
those equivalences. Every strong estimate is on a proper sector about the
negative real axis, with its own radius and constants. The general weight
result applies only under the stated conditions, not to arbitrary weights.

## Deliberately unresolved

- Ordinary (k = 1) negative-direction Borel summability for quadratic feedback.
- A general critical-order summability theorem for p >= 2.
- Uniform estimates on the boundary rays or a verified Nevanlinna--Sokal domain.
- Sharp numerical remainder types and the best exponential error constant.
- Pointwise lower bounds for optimally truncated remainders.
- Multiplicative or signed coefficient equivalents for the inverse.
- Cancellation-sensitive signed/complex kernels, systems, and faster weights.

The literal kernel's positive-real divergence is not used to rule out all
possible analytic continuation or generalized summation in that direction.

## Computation and formal verification

The exact program checks finite coefficient identities, benchmarks, and
inequalities, through the recorded finite orders. High-precision numerical
checks are diagnostics, not interval certificates. Neither kind of check
establishes infinite-order asymptotics, sectorial existence, or summability.
No Lean implementation or Lean verification is supplied or claimed.

The final PDF was compiled through three resolving passes and visually
inspected. The final build has no undefined references and no overfull or
underfull box warnings. This is document QA, not mathematical proof verification.

## Originality

The coefficient-to-remainder bridge and its model-specific sharp directional
summability consequences are proposed research contributions. The article
makes no certified global priority claim and does not call a classical method
an invention. Independent mathematical review remains appropriate.
