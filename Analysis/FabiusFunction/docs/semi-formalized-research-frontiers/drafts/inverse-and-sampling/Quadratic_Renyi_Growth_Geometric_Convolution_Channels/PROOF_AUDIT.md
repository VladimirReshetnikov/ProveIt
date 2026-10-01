# Proof and validation audit

## Target and provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `a4268e78ebd0f6bf71ba609c07f4b3415748f532`

Predecessor path:
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Nuclear_Bayesian_Operators_Fabius_Rvachev_Laws/article.tex`

Returned predecessor blob SHA: `960890e910fcb8bfb857dfb0e08b4303c3f139f5`

The predecessor proves divergence of the excess Rényi information at fixed
orders above two, but expressly leaves its growth rate open. The present
article proves a quadratic term, an explicit linear correction, and a
logarithmic-square error. The theorem is a solution of that stated
repository-local question. No exhaustive literature-priority claim is made.

The predecessor's [-1,1] normalization is related to this article by separate
invertible affine changes of the source and prefix variables. The Rényi
divergence is unchanged. This relationship is stated in Section 1.2.

## Analytic dependency chain

1. **Exact channel identities.** An independent tail copy gives the joint-density
   formula and the normalized nonnegative moment integral. Every Jacobian and
   the factor converting excess information into total information is retained.
2. **Positive simplex geometry.** The finite beta prefix is compared with an
   unrestricted power-simplex density using a Dirichlet expectation. Integrands
   are defined to be zero outside the valid support before real powers are
   evaluated. The restrictions theta_0,theta_1 >= 1 are used explicitly.
3. **Full endpoint density.** A prefix length of order `(T+log T)/L` gives upper
   and lower density comparisons with bounded logarithmic error. Stirling
   expansion then determines the quadratic, `T log T`, and linear terms.
4. **Two saddle variables.** The allocation integral is uniformly compared to a
   beta integral. Global radial tail bounds precede the local comparison saddle.
   Only the explicit comparison function is differentiated, never its remainder.
5. **Cancellation.** The `m log m` terms cancel, as do the innovation endpoint
   normalization and the contraction parameter in the linear coefficient.
6. **Assembly.** A conditional-density inequality bounds the entire middle
   region. A strictly positive quadratic gap makes it negligible. Comparing
   both endpoints selects their maximum innovation exponent.
7. **Tilted laws.** Restricted versions of the same integrals prove radial
   large deviations at speed m^2 and allocation large deviations at speed m.
   The radial-factor normalization in the allocation endpoint bound is
   evaluated explicitly enough to ensure only an O(m) logarithmic cost.

## Executed exact checks

The retained `checks/verification.json` reports:

- the quadratic identity has symbolic residual zero;
- the complete general-parameter linear cancellation has residual zero;
- the proposed allocation has derivative zero in the entropy objective;
- 24 exact dyadic refinement identities hold;
- density values f(1/2)=2, f(1/4)=1, f(1/8)=5/36 hold;
- the moment recurrence gives mean 1/2 and variance 1/36.

These are finite consistency checks. They are not formal verification of the
analytic asymptotic proof.

## Numerical diagnostics

The point diagnostics use exact dyadic rational densities for m in
{8,12,16,24,32,48,64,96}, followed by high-precision logarithms. A point integrand
value is not its integral and is labeled accordingly in the article.

Windowed Gauss–Legendre runs were executed at 24 and 32 nodes per axis for m=8
and m=12, using 80 and 100 decimal digits, respectively. The resulting endpoint
information-scale estimates are approximately:

| m | 24 nodes | 32 nodes |
|---|----------|----------|
| 8 | 24.9467079713 | 24.9467514085 |
| 12 | 53.8061366408 | 53.8061793012 |

The differences are a stability diagnostic only. The retained JSON records the
window and the omitted-density-term bound. No certified quadrature-error or
rounding enclosure is supplied, and these are not full-information values.

## PDF and package checks

The source compiled to a 19-page PDF with no unresolved references, citations,
LaTeX warnings, or overfull boxes on the final pass. All pages were rendered
with Poppler and visually inspected. The article and its generated table can
be rebuilt without rerunning Python. Package hashes are in `SHA256SUMS`.

*Amendment (ProveIt, 2026-09-30):* the delivered checksum ledger `SHA256SUMS`
(11 entries) was verified in full on filing (batch 65) and not kept; the
delivered archive remains in the repository history (see
`docs/incoming/README.md`, batch 65 row). The PDF was later rebuilt with
editorial notes (see the README's "Editorial amendments").

## Limits not silently promoted to theorems

No result is asserted uniformly as alpha decreases to two, q increases to one,
alpha tends to infinity, or beta parameters vary. Beta exponents below one,
more general endpoint masks, finer lattice corrections, fluctuation limits,
and the critical crossover remain explicitly proposed research problems.
No Lean or Rocq verification, independent peer review, or exhaustive novelty
certification was performed. No existing repository file was modified.
