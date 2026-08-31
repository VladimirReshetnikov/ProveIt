# Inverse and sampling

Most documents in this theme are organized one level deeper by their principal
overlap:

- [`comb-interpolation/`](comb-interpolation/) — additive and geometric comb
  interpolation, quadrature, extrapolation, and stability;
- [`inverse-asymptotics-and-computability/`](inverse-asymptotics-and-computability/)
  — inverse germs, endpoint asymptotics, self-sampling, effective moduli, and
  certified computation;
- [`analyticity-and-elementarity/`](analyticity-and-elementarity/) —
  nowhere-analytic inverse iterates and elementary-representation
  obstructions.

The cross-cutting information-geometry intake lives directly at
[`fabius_information_frontier/`](fabius_information_frontier/). Neighboring
themes provide techniques or related forward results, but these documents
remain in `inverse-and-sampling` when inverse behavior, sampling geometry, or
their information geometry is the principal subject. The
inverse-iterate report retains its explicit reconciliation link to the forward
iterate report under `representations/`.

[`Inverse_Fabius_Analyticity_Asymptotics_and_Computability/`](Inverse_Fabius_Analyticity_Asymptotics_and_Computability/)
is a consolidation workspace for five of these live source packages.  It
currently contains provenance and a reproducible source-result inventory, not
a canonical TeX/PDF deliverable.  The five source packages remain authoritative
and will not be retired until every result and unique asset has a recorded
disposition and a matching consolidated PDF passes the publication gate.

## Non-comb source-only merge status (2026-08-31)

The canonical-notation integration changed the five live non-comb TeX roots
listed below. The remote reorganization supplied a synchronized TeX/PDF/ledger trio
for `analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function`, so
that package is not included in the stale-artifact table below.
By explicit integration policy, none of the listed same-stem PDFs was rebuilt;
operational ledgers covering changed roots were not refreshed except as stated.
The relinked 12-entry ledger for
`inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers` now
fails only its root-TeX row, while its other eleven rows pass. Its retained PDF
is not a rendering of the changed source.
The PDFs and their page/font/build facts below are therefore retained
historical artifacts, not claimed renderings of the current sources.

| Root report | Current TeX lines | Current TeX SHA-256 | Retained PDF | Operational-ledger status |
|---|---:|---|---:|---|
| `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders` | 1,979 | `0709a513017d42b94f931f6e4a2b0ac396464497c8fa75ef660545f4ab163507` | 23 pages | no live root-pair ledger |
| `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report` | 2,937 | `d161226599c27c3a7b7818bcf9d30c226be66fdf2f46d359735d4f95f5044ae6` | 42 pages | TeX and README rows pending; other four pass |
| `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers` | 6,607 | `d5f5ba096af58634fe0693bd4731b10898a85ad38204c661edde2ddbe38ed04a` | 100 pages | TeX row pending; other eleven pass |
| `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic` | 1,742 | `eda8c676e00a68c1e57e36ee22bfb3502cd56dd95f5630efcaf6a7f0f3b3d3d5` | 26 pages | TeX and README rows pending; other thirteen pass |
| `fabius_information_frontier` | 2,137 | `a8dd383ef450f4a6338990115b982945dc7f36674f7a65f3e623ca2002883296` | 30 pages | TeX and README rows pending; other seventeen pass |

Package README edits that record this source-only state also make their own
operational-ledger rows intentionally pending.  Arrival ledgers and historical
PDF hashes remain immutable and are not affected by this note.

Current members and recent intake:

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

- [`comb_interpolation_synthesis/`](comb-interpolation/comb_interpolation_synthesis/),
  *Comb Interpolation and Sampling Frontiers: Additive and Geometric Combs in
  the Fabius--Rvachev System*, is the canonical synthesis of the former
  additive-dyadic volume and the three geometric-comb manuscripts. Common
  Gaussian-Pascal, Jackson--Newton, Lagrange, stability, and Fabius boundary
  material is stated once; genuinely distinct modal, Mellin,
  regular-variation, spline, reciprocal-product, Euler--Maclaurin, Ruffa,
  Thue--Morse, and interpolation results retain their proofs. The additive
  source had already absorbed nine nested manuscript packages; their duplicate
  documentation and the three geometric wrappers have now been retired.
  Unique computational evidence is preserved by source slug. The source
  inventory is pinned to
  `73f0b373126ef22a3b5dccadfa7b99d61d445345`; its 180-row disposition and
  151-row historical-ledger audit are recorded in the canonical package.
  Final PDF and full-validator success remain separate publication gates.
- [`fabius_information_frontier/`](fabius_information_frontier/), *Exact
  Information Geometry and New Frontiers for the Fabius--Rvachev System*
  (retained submitted 30-page PDF; current 2,137-line TeX), was filed on
  2026-08-30 from `fabius_information_frontier_report.zip` (outer SHA-256
  `41f9aba6eb85bb173827f13cb6b7b1d54b7ea9346faf7c9e5b1af859bbd42ec7`)
  and moved here from `frontier-compilations` in the latest thematic
  reorganization. Its immutable 18-entry arrival ledger verified the submitted
  payload and is preserved byte-for-byte. The operational ledger was not
  refreshed after the source-only notation migration: its TeX and README rows
  are pending and its other seventeen rows pass. The retained PDF was not
  rebuilt from the current source. It remains an archival intake rather than a
  claim-level acceptance; manuscript theorem labels do not establish Lean
  verification.

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
  `d161226599c27c3a7b7818bcf9d30c226be66fdf2f46d359735d4f95f5044ae6`;
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

This theme combines consolidated volumes with retained standalone reports;
the subgroup READMEs are the authoritative navigation after each synthesis.

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

The current merged root has 6,607 lines. Its retained 100-page PDF was not
rebuilt after the notation merge. The relinked 12-entry ledger under
`assets/Fabius_Inverse_Frontier_Report_Source_and_PDF/` fails only the current
root-TeX row; its other eleven rows pass.

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

## `comb-interpolation/comb_interpolation_synthesis/`

*Comb Interpolation and Sampling Frontiers* is the canonical editorial union
of the former additive-dyadic volume and all three geometric-comb manuscripts.
The additive source already represented nine absorbed packages: six
comb-sum/interpolation sources, two Euler--Maclaurin/exhaustion sources, and
one Bernoulli--Ruffa phase-calculus source. The new synthesis uses the strongest
Gaussian-Pascal and Jackson--Newton development as its finite geometric spine,
deduplicates common derivations, and preserves the genuinely additional
modal, Mellin, regular-variation, spline, Fabius-transform, reciprocal-product,
quadrature, phase, Thue--Morse, and interpolation results.

The pre-retirement state is pinned to
`73f0b373126ef22a3b5dccadfa7b99d61d445345`. Unique scripts, exact tables,
data, text outputs, and PNG figures are retained by historical source slug;
old manuscript wrappers, report/preview PDFs, stale package ledgers, and
duplicated documentation are retired. The canonical package records a
180-row source disposition and a 151-row historical-ledger audit. Its README
and provenance file describe the evidence boundary. Final PDF and full
validator success are not claimed until the separate publication gates pass.

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
`d161226599c27c3a7b7818bcf9d30c226be66fdf2f46d359735d4f95f5044ae6`).
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
and 8,389 public declarations with zero documentation/header gaps.

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
