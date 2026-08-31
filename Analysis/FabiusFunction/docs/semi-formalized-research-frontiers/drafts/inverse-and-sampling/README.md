# Inverse and sampling

New standalone intake members:

- [`Non_Elementarity_of_the_Fabius_Function/`](Non_Elementarity_of_the_Fabius_Function/),
  *The Fabius Function and Its Inverse are Not Elementary* (14 A4 pp,
  1068 source lines), filed on 2026-08-31 from the bare directory
  `drafts/incoming/Non_Elementarity_of_the_Fabius_Function/`.  Origin commit
  `7bd49a7f7` had moved the byte-identical TeX/PDF pair from the former root
  documentation path into the intake queue because full formalization had not
  yet been established.  No archive or submitted checksum ledger accompanied
  that move, so the repository-generated two-entry `ARRIVAL_SHA256SUMS.txt`
  records and verifies both delivered payloads.  The TeX was already LF; the
  supplied PDF is A4, uses embedded/subset Libertinus and Type-1 mathematical
  fonts, and has no Type-3 font.  Its title and abstract concern the analytic
  locus, elementary and algebraic branches, and the inverse Fabius function,
  so it belongs in this inverse-facing group.  An older same-stem study remains
  under `docs/archive/standalone-studies/`, but neither its TeX nor its PDF is
  byte-identical to this later expanded package; intake preserves both and
  defers any supersession decision.  The manuscript presents itself as a
  human-readable account of a formal development, but quick intake did not
  perform a claim-by-claim Lean audit; its status remains standalone and
  unreviewed until that post-publication crosswalk.

- [`geometric_comb_q_fabius_report/`](geometric_comb_q_fabius_report/),
  *Geometric-Comb Interpolation, Gaussian Pascal Transforms, and the
  Fabius--Rvachev Boundary Layer* (65 pp), arrived on 2026-08-30 from
  `geometric_comb_q_fabius_report.zip` (outer SHA-256
  `d7a84fdad1cc0e98f3e2d9d6e6a101cdae2a070a190a957cd15d761ec765a54c`).
  All 16 submitted payload hashes verified; two CSV entries were refreshed
  after CRLF-to-LF repository normalization. It belongs beside the geometric
  and dyadic comb reports below, while cross-linking the q-Pochhammer monograph.
  It remains standalone pending post-publication assessment and a Lean
  crosswalk; its formalization section is explicitly future work. Manuscript
  labels do not establish Lean verification.

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

- [`geometric_comb_interpolation_report-3/`](geometric_comb_interpolation_report-3/),
  *Interpolation on a Geometric Comb: Lagrange Filters, Jackson--Newton
  Series, q-Analogues, and the Fabius--Rvachev Bridge* (36 pp), arrived on
  2026-08-30 from `geometric_comb_interpolation_report-3.zip` (outer SHA-256
  `89c9de31b9b78b614c13d5a3ff24ae41b73ef6704a9daef77ba724b396e90fa0`).
  All 20 submitted payload hashes verified; four CSV entries were refreshed
  after CRLF-to-LF repository normalization. This is a distinct later
  arrival, not a byte duplicate of `geometric_comb_interpolation_report/`,
  and no submitted payload hash matches either existing geometric-comb report.
  It is filed in a collision-safe wrapper without superseding either package.
  The A4 report retains 11 embedded Type-3 plot-font rows. It remains
  unreviewed pending post-publication reconciliation with the earlier report
  and a claim-by-claim Lean crosswalk; manuscript labels do not establish
  Lean verification.

- [`Inverse_Fabius_Computability_Report/`](Inverse_Fabius_Computability_Report/),
  *Computability of the Inverse Fabius Function* (41 A4 pp, 2923 source
  lines after combining the parallel equality/rigidity and
  logarithmic-modulus post-publication branches; those branch checkpoints
  were 39 pp and 2801 lines and 39 pp and 2743 lines, respectively, after
  the common 37 pp and 2621 lines and earlier 34 pp and 2446 lines; 29 pp
  and 2157 lines at intake), arrived on
  2026-08-30 from `Inverse_Fabius_Computability_Report.zip` (outer SHA-256
  `755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1`).
  All five submitted payload hashes verified and every text payload was
  already LF. A post-publication claim-by-claim reassessment now crosswalks
  the global weak and maximal-domain strict fixed-length-increment shape,
  complete endpoint equality locus, inverse-gap
  rigidity, exact-supremum, subadditivity, and effective-injectivity layers to
  compiler-validated
  [`InverseModulus.lean`](../../../../Lean/FabiusFunction/InverseModulus.lean).
  The source now also exhaustively crosswalks all fourteen public declarations
  in
  [`FabiusInverseEffectiveContinuity.lean`](../../../../Lean/FabiusFunction/FabiusInverseEffectiveContinuity.lean):
  a one-term recurrence lower bound stronger than the report's box estimate,
  the exact numerical `Delta_r` inequality, strict and closed versions of the
  Delta/factorial dyadic inverse moduli, primitive-recursive denominators, and
  `EffectivelyUniformContinuous` with the simple `r=n` factorial witness. The
  source further exhaustively crosswalks all eighteen public declarations
  (three definitions and fifteen theorems) in
  [`FabiusInverseLogarithmicModulus.lean`](../../../../Lean/FabiusFunction/FabiusInverseLogarithmicModulus.lean):
  the primitive-recursive least order `r(n)`, its binary-length and minimality
  laws, the report-exact Delta and stronger factorial denominators at that
  order, their primitive recursiveness and comparison, strict and closed-input
  reciprocal moduli, and `EffectivelyUniformContinuous` with either witness.
  The probabilistic box-event proof itself, exact ceiling `d_*`, tolerant
  bisection, sequential computability, the combined computable-real-function
  theorem, and precision asymptotics remain open Lean work. The `d_*` claim
  remains denominator-minimal only for the fixed dyadic proxy `2^{-r(n)}`, not
  the weaker target `1/n`. The synchronized three-pass 41-page A4 PDF has
  embedded/subset fonts, includes Libertinus, and is Type-3-free; all five
  active checksum entries verify.

- [`inverse_fabius_iterates_nowhere_analytic/`](inverse_fabius_iterates_nowhere_analytic/),
  *Nowhere Analyticity of Every Positive Compositional Iterate of the Inverse
  Fabius Function* (24 A4 pp, 1730 source lines), arrived on 2026-08-30 from
  `inverse_fabius_iterates_nowhere_analytic.zip` (outer SHA-256
  `8b1c05d59e120ecd20d69cd5aeb0009639f2f3b9a6c9fef32bdf82270eee16bd`).
  All 13 submitted payload hashes verified; `spine_diagnostic.csv` was
  refreshed after CRLF-to-LF repository normalization. It remains standalone
  pending post-publication reconciliation with
  [`../representations/fabius_iterates_nowhere_analytic/`](../representations/fabius_iterates_nowhere_analytic/)
  and further Lean work. Its source now crosswalks the complete finite
  positive-list defect API in `PartitionDefect.lean`, while the set-partition
  bridge, weighted Bell/spine asymptotics, and principal forward/inverse
  iterate claims remain paper-only.

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
