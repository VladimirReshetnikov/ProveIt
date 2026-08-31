# Inverse and sampling

Nine document bundles live in this theme, organized one level deeper by their
principal overlap:

- [`comb-interpolation/`](comb-interpolation/) — additive and geometric comb
  interpolation, quadrature, extrapolation, and stability;
- [`inverse-asymptotics-and-computability/`](inverse-asymptotics-and-computability/)
  — inverse germs, endpoint asymptotics, self-sampling, effective moduli, and
  certified computation;
- [`analyticity-and-elementarity/`](analyticity-and-elementarity/) —
  nowhere-analytic inverse iterates and elementary-representation
  obstructions.

The cross-cutting information-geometry intake now lives under
[`../frontier-compilations/fabius_information_frontier/`](../frontier-compilations/fabius_information_frontier/),
whose broader geometric-uniform scope is a better thematic fit. The
inverse-iterate report here retains its explicit reconciliation link to the
forward-iterate report under `representations/`.

## Source-only merge status (2026-08-31)

The local canonical-notation integration changed eight living TeX roots in this
group. The remote reorganization supplied a synchronized TeX/PDF/ledger trio
for `analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function`, so
that package is not included in the stale-artifact table below.
By explicit integration policy, none of their same-stem PDFs was rebuilt and
none of the seven local operational ledgers that cover a changed root was
refreshed. The remote's relinked 12-entry ledger for
`inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers` is safe
to take unchanged and verifies 12/12 current files, but that integrity result
does not make its retained PDF a rendering of the changed source.
The PDFs and their page/font/build facts below are therefore retained
historical artifacts, not claimed renderings of the current sources.

| Root report | Current TeX lines | Retained PDF | Operational-ledger status |
|---|---:|---:|---|
| `comb-interpolation/Dyadic_Comb_Frontiers` | 5,648 | 66 pages | no live root-pair ledger |
| `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders` | 1,979 | 23 pages | no live root-pair ledger |
| `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report` | 2,937 | 42 pages | TeX row pending rebuild |
| `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers` | 6,608 | 100 pages | remote relinked ledger passes; PDF remains historical |
| `comb-interpolation/geometric_comb_interpolation_report` | 2,360 | 32 pages | TeX row pending rebuild |
| `comb-interpolation/geometric_comb_interpolation_report-3` | 2,736 | 36 pages | TeX/README/relocated-audit rows pending |
| `comb-interpolation/geometric_comb_q_fabius_report` | 3,554 | 68 pages | TeX row pending rebuild |
| `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic` | 1,742 | 26 pages | TeX row pending rebuild |

Package README edits that record this source-only state also make their own
operational-ledger rows intentionally pending.  Arrival ledgers and historical
PDF hashes remain immutable and are not affected by this note.

New standalone intake members:

- [`Non_Elementarity_of_the_Fabius_Function/`](analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/),
  *The Fabius Function and Its Inverse are Not Elementary: Density of the
  Analytic Locus under Algebraic Branches and Inversion* (14 A4 pp; 1,068
  source lines at intake and 1,057 after the notation migration), was
  reclassified on 2026-08-31 from the former top-level
  `docs/Non_Elementarity_of_the_Fabius_Function/` pair through
  `drafts/incoming/` and initially filed here without changing either submitted
  payload. The bare two-file package supplied no archive or checksum ledger.
  The intake hashes were PDF `ab722e11...` and TeX `3c3c2f48...`; the active
  repository-added `SHA256SUMS` was refreshed after the post-publication
  semantic-notation migration and verifies the current TeX/PDF pair. Its TeX
  source remains LF, and its structurally readable, unencrypted PDF uses embedded/subset
  fonts, includes Libertinus, and has no Type 3 font. The
  title and abstract place its forward/inverse non-elementarity and analytic-
  locus material with the inverse-function reports in this group. An older
  same-stem study remains under `docs/archive/standalone-studies/`, but neither
  its TeX nor its PDF is byte-identical to this later expanded package; both
  are preserved and any supersession decision is deferred. It remains
  standalone pending post-publication claim-level reassessment and verification
  of its Lean crosswalk; manuscript theorem labels and the document's own
  formalization description do not independently establish current Lean
  verification.

- [`geometric_comb_q_fabius_report/`](comb-interpolation/geometric_comb_q_fabius_report/),
  *Geometric-Comb Interpolation, Gaussian Pascal Transforms, and the
  Fabius--Rvachev Boundary Layer* (retained 68-page A4 PDF; current
  3,554-line TeX; 637-line deterministic experiment). No attributable source
  archive remains, so no outer-archive hash is inferred; the immutable
  submitted ledger preserves the arrival state. The 20-entry operational
  ledger was intentionally not refreshed after the source-only merge: its TeX
  and README rows are pending and the other 18 rows pass. A pinned CPython
  3.13.14 replay was byte-identical across all 11 generated artifacts. The
  retained A4/27 mm/Libertinus PDF was built in exactly three strict passes
  at the preceding publication checkpoint, but not from the current source,
  with every font embedded/subset and no Type 3 fonts. The finite Gaussian,
  complete-homogeneous, geometric-Lagrange, moment, condition-number,
  half-moment, and Rvachev-deconvolution layers are crosswalked to their named
  Lean declarations. The report-specific Jackson basis, arbitrary-point
  residual, analytic convergence, Lebesgue asymptotics, Fabius bounds, and
  Gaussian--Appell packaging remain manuscript-only; the two-sided gap,
  second-order Lebesgue, and Hermite-saddle claims remain conjectures, and the
  growing-order Hermite problem remains open. It belongs beside the geometric
  and dyadic comb reports below and cross-links the q-Pochhammer monograph;
  manuscript labels do not establish Lean verification.

- [`geometric_comb_interpolation_report/`](comb-interpolation/geometric_comb_interpolation_report/),
  *Interpolation on a Geometric Comb* (retained 32-page A4 PDF; current
  2,360-line TeX), is the canonical A4/27 mm/Libertinus edition of the report
  filed on 2026-08-30.
  The source archive is no longer available in the repository, but its
  preserved 11-entry arrival ledger records the arrival state. The 17-entry
  operational ledger was intentionally not refreshed after the source-only
  merge: its TeX and README rows are pending and the other 15 rows pass. A
  pinned CPython 3.13.14 replay reproduced all four
  CSV tables and three PNG figures byte-for-byte. Its 37 nonconjectural
  manuscript results, two conjectures, and five problems were hostile-audited;
  no fatal counterexample was found, the perpetuity-density proof was hardened,
  and the Lean crosswalk now distinguishes exact finite q-Lagrange/Gaussian
  infrastructure from the report-level interpolation and asymptotic claims.
  Its arbitrary-ratio interpolation layer belongs beside
  `Dyadic_Comb_Frontiers/` and cross-links to the finite q-Lagrange/Gaussian row in
  [`../exponents-and-q-series/q_pochhammer_q_binomial_monograph/`](../exponents-and-q-series/q_pochhammer_q_binomial_monograph/).
  The retained PDF was built in exactly three strict passes with
  embedded/subset fonts and no Type 3 fonts at the preceding checkpoint; it
  was not rebuilt from the current source. Manuscript labels do not establish
  Lean verification.

- [`geometric_comb_interpolation_report-3/`](comb-interpolation/geometric_comb_interpolation_report-3/),
  *Interpolation on a Geometric Comb: Lagrange Filters, Jackson--Newton
  Series, q-Analogues, and the Fabius--Rvachev Bridge*, is a distinct 36-page
  A4 intake filed from
  `geometric_comb_interpolation_report-3.zip` (1,296,171 bytes; SHA-256
  `89c9de31b9b78b614c13d5a3ff24ae41b73ef6704a9daef77ba724b396e90fa0`).
  Its submitted 20-entry ledger is preserved as arrival provenance. After
  four CSV files were normalized from CRLF to LF, the operational ledger was
  expanded to 25 entries. It was intentionally not refreshed after the later
  source-only notation migration and thematic relocation: its TeX, README,
  and intake-audit rows are pending and the other 22 rows pass. The current
  TeX has 2,736 lines; the retained 36-page
  submitted PDF was not rebuilt. This is not a reship of the neighboring comb
  report: none of their non-ledger payload hashes coincide. In accordance
  with the incoming-archive gate, replay, hostile claim audit, dependency
  pinning, canonical-preamble normalization, rebuild, and page-by-page visual
  audit are deliberately deferred until after this archival checkpoint is
  committed and pushed.

- [`Inverse_Fabius_Computability_Report/`](inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/),
  *Computability of the Inverse Fabius Function* (retained 42-page A4 PDF;
  current 2,937-line source), arrived on
  2026-08-30 from `Inverse_Fabius_Computability_Report.zip` (outer SHA-256
  `755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1`).
  All five submitted payload hashes verified and every text payload was
  already LF. A post-publication claim-by-claim reassessment now crosswalks
  the structural least-mass, global weak and maximal-domain strict
  fixed-length-increment shape, complete endpoint equality locus, inverse-gap
  rigidity, exact-supremum, subadditivity, and effective-injectivity layers to
  compiler-validated
  [`InverseModulus.lean`](../../../../Lean/FabiusFunction/InverseModulus.lean).
  The post-publication strict/equality extension adds eleven declarations:
  six support/strict results (`fabiusIntervalMass_eq_zero_of_add_nonpos`,
  `fabiusIntervalMass_eq_zero_of_one_le`,
  `strictMonoOn_fabiusIntervalMass_firstHalf`,
  `strictAntiOn_fabiusIntervalMass_secondHalf`,
  `fabiusReal_lt_fabiusIntervalMass_of_mem_Ioo`, and
  `fabiusReal_sub_lt_sub`) and five equality classifications
  (`fabiusIntervalMass_eq_fabiusReal_iff`, `fabiusReal_sub_eq_sub_iff`,
  `fabiusReal_add_eq_iff`, `fabiusInv_sub_eq_sub_iff_of_mem_Icc`, and
  `abs_fabiusInv_sub_eq_iff_of_mem_Icc`).
  The source now also exhaustively crosswalks all fourteen public declarations
  in
  [`FabiusInverseEffectiveContinuity.lean`](../../../../Lean/FabiusFunction/FabiusInverseEffectiveContinuity.lean):
  a one-term recurrence lower bound stronger than the report's box estimate,
  the exact numerical `Delta_r` inequality, strict and closed versions of the
  Delta/factorial dyadic inverse moduli, primitive-recursive denominators, and
  `EffectivelyUniformContinuous` with the simple `r=n` factorial witness. It
  further exhaustively crosswalks all eighteen public declarations (three
  definitions and fifteen theorems) in
  [`FabiusInverseLogarithmicModulus.lean`](../../../../Lean/FabiusFunction/FabiusInverseLogarithmicModulus.lean):
  the primitive-recursive least order `r(n)`, its binary-length and minimality
  laws, the report-exact Delta and stronger factorial denominators at that
  order, their primitive recursiveness and comparison, strict and closed-input
  reciprocal moduli, and `EffectivelyUniformContinuous` with either witness.
  The probabilistic box-event proof itself, exact ceiling `d_*`, tolerant
  bisection, sequential computability, the combined computable-real-function
  theorem, and precision asymptotics remain open Lean work. The `d_*` claim
  remains denominator-minimal only for the fixed dyadic proxy `2^{-r(n)}`, not
  the weaker target `1/n`. The current 2,937-line source has SHA-256
  `3ee69aa0c27486d5005e4d5f8448b36a8133083c8b79df51e9d08a5af56880b5`;
  the retained 42-page A4 PDF has 711,374 bytes and SHA-256
  `5a9976f9ece840d1b8456b4ea3753c36e369cbade8caff1c04158cc7d33cff75`.
  That PDF was built at the preceding checkpoint in exactly three strict
  serial passes, with repaired
  author metadata, every font embedded/subset (22 fonts), Libertinus present,
  and no Type 3 fonts. The immutable five-entry arrival ledger verifies the
  submitted payload. The six-entry operational ledger was intentionally not
  refreshed after the source-only merge: its TeX and README rows are pending
  and the other four rows pass.

- [`inverse_fabius_iterates_nowhere_analytic/`](analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/),
  *Nowhere Analyticity of Every Positive Compositional Iterate of the Inverse
  Fabius Function* (retained 26-page A4 PDF; current 1,742-line source),
  arrived on 2026-08-30 from
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
ideas, in three consolidated volumes and six retained standalone reports.

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

## `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/`

The current merged root has 6,608 lines. Its retained 100-page PDF was not
rebuilt after the notation merge. The remote's relinked 12-entry ledger under
`assets/Fabius_Inverse_Frontier_Report_Source_and_PDF/` matches the current
source, retained PDF, and all ten supporting files; it is accepted as an
integrity receipt, not as evidence that the PDF was rebuilt from this source.

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

## `comb-interpolation/Dyadic_Comb_Frontiers/`

The current merged root has 5,648 lines. Its retained 66-page PDF was not
rebuilt after the notation merge, and this volume has no live checksum ledger
covering the root TeX/PDF pair.

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

## `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`

The current merged root has 1,979 lines. Its retained 23-page PDF was not
rebuilt after the notation merge, and this volume has no live checksum ledger
covering the root TeX/PDF pair.

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

## `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`

Filed 2026-08-30 from `Inverse_Fabius_Computability_Report.zip` (689,198
bytes; SHA-256
`755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1`).
The current canonical source has 2,937 lines (SHA-256
`3ee69aa0c27486d5005e4d5f8448b36a8133083c8b79df51e9d08a5af56880b5`).
The retained historical 42-page A4/27 mm/Libertinus PDF has 711,374 bytes
(SHA-256
`5a9976f9ece840d1b8456b4ea3753c36e369cbade8caff1c04158cc7d33cff75`).
It was built at the preceding checkpoint in exactly three strict serial
passes with all 22 fonts
embedded/subset, Libertinus present, and no Type 3 fonts.  The report gives
self-contained proofs of the structural least-interval-mass and exact
inverse-modulus identities, the elementary endpoint-mass estimate,
tolerant-bisection realizer, inverse-computability packaging, and optimal
input-bit law.  `InverseModulus.lean` now adds eleven strict/equality
declarations: six support/strict results covering the two constant tails,
the two strict fixed-length half-shapes, and strict interior mass, together
with five endpoint/equality classifications for fixed-length mass,
superadditivity, and ordered and absolute inverse gaps.  The closed
`Delta_r` estimate, recursive-modulus packaging, tolerant bisection,
sequential computability, and input-bit asymptotics remain paper-level.  The
crosswalk also identifies the already formalized forward spline/computability,
strict shape, inverse identities/calculus, exact dyadic evaluation, and leading
inverse endpoint equivalent; explicit periodic and all-orders inverse
reversion remain frontier-document results.  The exact-rational supplement
reproduces its captured output byte for byte.  Original five-file hashes are
preserved in `ARRIVAL_SHA256SUMS.txt`. The six-entry `SHA256SUMS.txt` was not
refreshed after the source-only merge: its TeX and README rows are pending and
the other four rows pass. The live union audit scans 615 Lean modules
and 8,383 public declarations with zero documentation/header gaps.

## `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`

Filed 2026-08-30 from `inverse_fabius_iterates_nowhere_analytic.zip`
(1,137,032 bytes; SHA-256
`8b1c05d59e120ecd20d69cd5aeb0009639f2b3b9a6c9fef32bdf82270eee16bd`).
The current source has 1,742 lines. Its retained 26-page
A4/27 mm/Libertinus inverse-iterate companion derives
nowhere analyticity and formal-radius transport from the corrected forward
iterate report, then proves the affine but nonrepresenting center jet and the
iterated endpoint obstruction.  The inverse-nowhere-analytic conclusion is
already a corollary of that forward report and is not independent novelty.
Lean status is limited to the existing one-fold inverse analytic locus and
one-fold endpoint Hölder obstruction; the higher iterates, formal-radius
transport, all-order center jet, and iterated endpoint scale remain
manuscript-only.  The hostile audit retains 19 nonconjectural labelled results,
quarantines three stale, false, or duplicate conjecture claims as warnings,
and leaves only two explicitly unformalized conjectures. The pinned numerical
replay reproduced all 7 generated outputs byte for byte before repository LF
normalization; it proves none of the analytic claims. The submitted 13-entry arrival ledger is preserved as
`SHA256SUMS.arrival.txt` and verified 13/13 before normalization. The 15-entry
`SHA256SUMS.txt` was intentionally not refreshed after the source-only merge:
its TeX and README rows are pending and the other thirteen rows pass.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and previous paths.
