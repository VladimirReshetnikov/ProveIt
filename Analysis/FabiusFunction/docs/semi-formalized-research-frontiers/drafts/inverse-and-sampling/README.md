# Inverse and sampling

New standalone intake members:

- [`geometric_comb_interpolation_report/`](geometric_comb_interpolation_report/),
  *Interpolation on a Geometric Comb* (34 pp), arrived on 2026-08-30 from
  `geometric_comb_interpolation_report_bundle.zip` (outer SHA-256
  `9a2e33f6a7dc3ac4c30b0da212349b9d91b1da6dd2fabacce14329a6458ade12`).
  All 11 submitted payload hashes verified; four CSV entries were refreshed
  after CRLF-to-LF repository normalization. Its arbitrary-ratio interpolation
  layer belongs beside `Dyadic_Comb_Frontiers/` and cross-links to the finite
  q-Lagrange/Gaussian row in
  [`../exponents-and-q-series/q_pochhammer_q_binomial_monograph/`](../exponents-and-q-series/q_pochhammer_q_binomial_monograph/).
  It remains standalone pending post-publication assessment and a Lean
  crosswalk; manuscript labels do not establish Lean verification.

- [`Inverse_Fabius_Computability_Report/`](Inverse_Fabius_Computability_Report/),
  *Computability of the Inverse Fabius Function* (29 pp), arrived on
  2026-08-30 from `Inverse_Fabius_Computability_Report.zip` (outer SHA-256
  `755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1`).
  All five submitted payload hashes verified and every text payload was
  already LF. It remains standalone pending post-publication assessment and a
  Lean crosswalk; the newly submitted bridge is not thereby Lean-verified.

- [`inverse_fabius_iterates_nowhere_analytic/`](inverse_fabius_iterates_nowhere_analytic/),
  *Nowhere Analyticity of Every Positive Compositional Iterate of the Inverse
  Fabius Function* (23 pp), arrived on 2026-08-30 from
  `inverse_fabius_iterates_nowhere_analytic.zip` (outer SHA-256
  `8b1c05d59e120ecd20d69cd5aeb0009639f2f3b9a6c9fef32bdf82270eee16bd`).
  All 13 submitted payload hashes verified; `spine_diagnostic.csv` was
  refreshed after CRLF-to-LF repository normalization. It remains standalone
  pending post-publication reconciliation with
  [`../representations/fabius_iterates_nowhere_analytic/`](../representations/fabius_iterates_nowhere_analytic/)
  and a Lean crosswalk; its own status note says the principal claims have not
  been translated into Lean.

The inverse function's frontiers and the sampling/deconvolution circle of
ideas, in two consolidated volumes.

Post-snapshot formal status: `QuarterCatalanGerm.lean` now proves that the
distinguished rational quarter germ becomes the Catalan inverse of
`X + 4 X²` under the exact `9/4` parameter rescaling, together with the reverse
rescaling and every positive coefficient.  `FabiusInverseQuarterJet.lean`
then connects that quadratic inverse to the actual smooth inverse: its full
centered jet at `5/72 = F(1/4)` is the factorial-scaled Catalan coefficient
sequence, so `G^(m+1)(5/72) = (m+1)! (-4)^m C_m`.  This is equality of all
derivatives, not local analytic equality.  A named nonzero flat-remainder
decomposition remains open.  Beyond the quarter specialization, the
general-dyadic analytic/algebraic shadow, convergence and identification of
the inverse Taylor series, and the Bell--Lagrange formula also remain open.

## `Inverse_and_Sampling_Frontiers/`

Consolidated (2026-08-28) from:

- **Part I** — *Inverse Frontiers for the Fabius–Rvachev System*
  (formerly `Fabius_Inverse_Frontier_Report_Source_and_PDF/`);
- **Part II** — *Dyadic Inverse Germs and Barnes–Rvachev Deconvolution*
  (formerly `fabius_frontier_dyadic_inverse_barnes_report/`);
- **Part III** — *Dyadic Self-Sampling, Alias Superconvergence, and
  Rvachev–Appell Deconvolution*
  (formerly `Fabius_Dyadic_Self_Sampling_Frontier_Package/`).

The member drafts were absorbed verbatim (labels, citation keys, and
asset paths mechanically prefixed per part; no mathematical content
altered) and their directories deleted; provenance with SHA-256 hashes
is recorded in the volume itself, and git history is the archive.

## `Dyadic_Comb_Frontiers/`

Editorially merged (2026-08-28) from the six dyadic-comb drafts of the
second and third waves — three on comb sums/quadrature
(`Fabius_Dyadic_Comb_Sums_Report_Package/`,
`fabius-dyadic-comb-sums-report/`, `fabius_dyadic_comb_report_final/`)
and three on global polynomial interpolation
(`fabius_dyadic_interpolation_report/`, `fabius_interpolation_report/`,
`Fabius_Rvachev_Dyadic_Interpolation_Report/`).  Because the six
sources largely re-derived one another's core results, this volume is a
true merge (unified notation, one statement per shared theorem with the
best proof, all source-specific material retained) rather than a
part-per-source concatenation.  A seventh, an eighth, and a ninth source were absorbed 2026-08-28 as the
Bernoulli-periodization section of Part I — the tenth-wave
`Fabius_Euler_Maclaurin_Report_Package/` (*Euler–Maclaurin and
Exhaustion Quadratures for Fabius and Rvachev Moments*): shifted
corrected rules for general polynomial weights, composite-mesh 2-adic
termination and reflection reduction, phase-modulated first-defect
series with Fabius-side forced phases, the first-harmonic proof that
D(2r) > 0 for every r (settling the volume's spectral-positivity
conjecture, and with it the odd half of the sharp-threshold
conjecture), the closed Ruffa exhaustion tail with derivative-free
rational Richardson extraction, the base-b termination dichotomy, the
composite-mesh Rvachev quadrature (sharp by the companion polynomial
volume's scale classification), and the Thue–Morse moment-identity
family; and its independently written eleventh-wave twin
(`fabius_rvachev_exhaustion_euler_maclaurin_bundle/`, *Exhaustion,
Euler–Maclaurin, and Spectral Exactness for Fabius–Rvachev Monomial
Integrals*), merged into the same section: the exact all-mesh alias–Bernoulli identity (layer cake +
Faulhaber, valid below every threshold), the general-q first defect in
Bernoulli-moment and spectral forms with midpoint/upper parity
superconvergence one level below threshold, the Bernoulli-moment
identity β₂ₘ = (−1)ᵐ·2(2m)!·D(2m)/(2π)²ᵐ (the twin's
conjectured sign law now follows from the positivity theorem; up to
sign these are the polynomial volume's defect values ℰ₂ₘ₋₁(0)),
the one-correction half-interval Rvachev rule with its
termination/one-mode exhaustion dichotomy and exact two-level
recovery, the supergeometric odd-base bound, and the q=1/4
Gaussian-binomial filter form; and the twelfth-wave Bernoulli–Ruffa
phase–resolution calculus, whose multiple-angle domination lemma
|Φ(qℓ/2)| ≤ |Φ(q/2)|/ℓ settles the twisted-positivity question
and BOTH phase-classification conjectures (the parity-forced phases
are the only superconvergent shifts, at every level and every odd
part), and which adds finite phase cubature (Simpson/Boole/Gauss in
the phase variable — exact moment certificates with no Bernoulli
correction), the phase–resolution separation principle,
Thue–Morse–Bernoulli digital phase filters with exact top-mode
constants and root-of-unity/digit-mask generalizations, coherent
radix exhaustion along tag orbits, anisotropic tensor shells, and a
proved all-orders complex-power expansion.  Provenance with SHA-256 hashes and the
deduplication record are Appendix E of the volume; every source's
supporting files live under its `assets/`.  The absorbed draft
directories are deleted; git history is the archive.

## `Inverse_Endpoint_All_Orders/`

Editorially merged (2026-08-28) from the three same-topic
inverse-asymptotics drafts of the fourth, fifth, and sixth waves:
`inverse_fabius_all_orders_package/` (*Closed All-Orders Endpoint
Asymptotics for the Inverse Fabius Function*),
`inverse_fabius_asymptotics_report/` (*Complete Small-Argument
Asymptotics of the Inverse Fabius Function*), and
`inverse_fabius_asymptotics_package/` (*Complete Small-Argument
Asymptotics of the Inverse Fabius Function* — the Wright-omega
write-up).  The first two both prove the closed Lagrange–Bürmann
coefficient formula, the universal highest logarithm, the explicit
third correction, and the elasticity recurrence — stated once, with
the independently derived third corrections verified algebraically
identical.  Contributions kept per source: structure laws (top-jet
transfer, Fourier/strip algebra, phase-locked tomography, derivative
hierarchy, exact-dyadic-quantile numerics); the
constrained-partition saddle engine and the exact 2-adic completion
of the Laplace exponent (dyadic Bose tail, Mellin bridge, exact
saddle map); and the log-free Wright-omega carrier (bounded periodic
coefficients with no logarithms, g₁ = −Ψ and the universal 5/24,
convergent bare skeleton, conditional Gevrey transfer, and
carrier-comparison numerics reaching 1.1e−9 at n = 160).
Complements — and imports the prior inverse corrections of —
`Inverse_and_Sampling_Frontiers/`.  Absorbed directories deleted;
provenance with SHA-256 in the volume's Appendix C and
`assets/SHA256SUMS-absorbed.txt`.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and previous paths.
