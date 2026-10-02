# Integrated companion review

Reviewed 2 October 2026. This extends `independent-audit.md` to the integrated report, its auxiliary radius theorem, and its inverse formula.

**Reviewed TeX SHA-256:**

`1e0019196acafab4899ef5dc405f8d8906267c36f6d40faf8991193d19b108f5`

File: `a202061-sharp-deficit.tex`.

**Verdict: signed off for release at this source hash.** The integrated mathematical transcription, sharp leading logarithmic deficit, finite-height radius equivalent, and inverse coefficient are supported by the proofs. No unresolved mathematical gap was identified. This is an independent research audit, not formal proof-assistant or journal peer-review certification.

## Integrated transcription

The main proof preserves the audited constants, scaling, signs, exact-length constraints, terminal factor, and order of limits. In particular, it contains the finite-q uniform-limsup correction, the local-only positive Gaussian lower lemma, the absolute sine Taylor remainder, and the restriction 0 < B < alpha/3.

Before signoff, the following small transcription or exposition points were corrected:

- M is the rounded cube root, with the cube root inside the rounding brackets
- The conditional q shift is beta(d−1)
- The lower-radius comparison uses 0 < delta < 1
- The initial and terminal vectors have positive Perron projections; the initial vector need not itself be strictly positive
- The inward boundary windows are expressed in the actual increment d = 1+r−q
- The uniform moment-generating-function limit used in the radius proof is stated explicitly

## Auxiliary finite-height radius theorem

The claimed equivalent

log(rho_H/rho) ~ (alpha/2) log(H)/H

passes review independently of the global deficit theorem.

For each finite H, the displayed fixed-r formula gives rational positive transition entries analytic on |x| < 1. Positivity of the matrix for x > 0, strict entrywise increase, and divergence toward x = 1 yield a unique Perron crossing. The positive Perron projections prevent cancellation of the pole. The nonnegative Neumann expansion converges below that crossing, so the crossing is the generating-function radius, not merely a real singularity candidate.

At the lower comparison point, the fixed-q transfer estimate and q split at H/(log H)^2 give an unrestricted tilted row bound m_*+o(1) < 1. The upper tail is O(H^(−delta/2) log H), with the corrected restriction 0 < delta < 1.

At the upper comparison point, q in [H−2H^gamma,H−H^gamma] remains legal for every height in the selected strip. Transfer supplies mass at least c H^(−1+delta/2) per q. For fixed real u, expanding the same analytic transfer formula at the height tilt u/sqrt(q) gives

E exp(u d/sqrt(q)) → exp(nu u^2/2)

uniformly. The drift term is O(log H/sqrt(H)) and the cubic term is o(1). Hence each appropriate inward interval retains a positive fraction of the mass, including at the strip endpoints. The row lower bound c H^(gamma−1+delta/2) diverges for the stated gamma. Perron comparison gives the opposite radius inequality. There is no endpoint leakage or hidden lattice-local-limit requirement.

## Exact inverse coefficient

With lambda = log(mu), regular variation gives Phi(L/lambda) ~ lambda^(−1/3) Phi(L), where L = log Y. Substituting the two bracketing integers around

L/lambda + (C_* lambda^(−4/3) ± epsilon) Phi(L)

leaves logarithmic differences ±lambda epsilon Phi(L) + o(Phi(L)). Monotonicity then proves the stated inverse expansion. Integer rounding contributes O(1).

Independent high-precision reevaluation gives:

- lambda = 1.9873121275680721762265659126660998456…
- C_* = 2.2326253076128449221797647005258492735…
- C_* lambda^(−4/3) = 0.8935682576508949091246421894534132392…

These agree with the integrated report. The stated scope exclusions are correct: no multiplicative coefficient equivalent, second-order deficit, exact integer inverse rounding rule, or all-orders expansion is proved.

## Artifact checks

The rebuilt PDF has 10 pages. I visually inspected the affected construction and auxiliary-theorem pages, including the corrected rounding expression and actual-increment MGF paragraph; both rendered correctly. The observed PDF SHA-256 was `24ab7dfbd11e72e98216dc366ad7a73ef0e771352dd2f0a5c792abce1fa12251`.

The bundled foundation passed its SHA256SUMS check. All 40 non-build, non-cache files compared byte-for-byte equal with the frozen foundation directory, including its report, source, certificates, and audit. Transient build products were excluded from this comparison.
