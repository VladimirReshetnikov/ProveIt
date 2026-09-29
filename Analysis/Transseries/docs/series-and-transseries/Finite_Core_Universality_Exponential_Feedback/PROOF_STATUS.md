# Proof status and limits

## Proved in the article by conventional arguments

1. Exact positive Lagrange and one-tail marking identities.
2. A sharp finite-core cutoff for an exact power tail after finitely many
   nonnegative exceptions: one-tail/full coefficient ratio tends to one
   exactly when M(p-1)>1, and to zero when M(p-1)<=1.
3. Full multiplicative asymptotics for every fixed one-tail core, including
   insufficient cores; transfer to full coefficients for sufficient cores.
4. Conditional local Gaussian law and conditional central limit theorem for
   each fixed core; unconditional weak central limit theorem for sufficient
   cores. An unconditional local limit theorem is not asserted.
5. Explicit first correction for p>3/2; the superpolynomial quadratic factor;
   universality of the bare equivalent when p>2.
6. Coefficient ratios for all fixed p>1 and the least-formal-term index in the
   pure model. No corresponding analytic remainder bound is asserted.
7. Sharp inverse coefficient asymptotics in the pure model for p>2, including
   the first correction and eventual negative sign.
8. Exact linear response of a formal inverse to one marked tail.

## Conjectural or not covered

The quadratic inverse equivalent is conjectural. A full inverse finite-core
reduction for 1<p<=2 has not been established. Other future topics are signed
primitive weights, general regularly varying tails, p varying with n, growing
cores, quantitative unconditional local laws, explicit certified error bounds,
and sectorial optimal-truncation remainder or summability theorems.

## Dependencies

The coefficient identity and macroscopic localization are re-proved rather
than assumed from a previous unreviewed repository draft. The sufficient
cutoff uses convex slope transfer with a counted many-to-one map. The saddle
formula is proved independently for every fixed core. It then proves cutoff
necessity by an explicit two-mark contribution. Signed reversion uses a
separate endpoint-convolution argument; it does not reuse positivity after
inversion.

Classical tools: formal Lagrange inversion, the analytic implicit function
theorem, Cauchy's coefficient formula, Stirling estimates, convexity,
Gaussian integration and lattice Riemann sums.

## Verification status

There is no Lean proof in this package. Exact finite identities and floating
numerical diagnostics do not certify asymptotic theorems. The written proofs
have been checked internally during preparation; independent specialist review
is still needed before treating the proposed results as established literature.
No global originality or publication-priority claim has been certified.
