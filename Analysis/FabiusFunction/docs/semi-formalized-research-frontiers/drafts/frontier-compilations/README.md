# Frontier compilations

New standalone intake members:

- [`Geometric_Uniform_Convolutions_and_New_Frontiers/`](Geometric_Uniform_Convolutions_and_New_Frontiers/)
  is the title-derived filing of the generic source-only wrapper
  `drafts/incoming/fabius-frontier-report-H/`, committed directly by
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`.  The delivery consists of a
  single TeX manuscript, *Geometric Uniform Convolutions and New Frontiers
  around the Fabius--Rvachev System*: no PDF, README, code, figures, captured
  output, checksum file, or archive was supplied.  Quick intake repaired three
  form-feed control bytes that had replaced the backslash in `\frac`
  commands and added a repository-generated one-entry `SHA256SUMS`.

  Its q-deformed derivative formulas, Gaussian/Edgeworth layer,
  valuation-weighted zeros, non-Gevrey growth, and periodic Lambert endpoint
  program overlap several same-batch reports and the consolidated corpus.
  The source remains standalone pending post-publication compilation,
  claim-by-claim comparison, and a Lean crosswalk.  Nothing in the intake
  establishes that the TeX compiles or that any manuscript theorem is proved
  in Lean.

- [`fabius_information_frontier/`](fabius_information_frontier/),
  *Exact Information Geometry and New Frontiers for the Fabius--Rvachev
  System* (30 pp), arrived on 2026-08-30 from the rootless archive
  `fabius_information_frontier_report.zip` (outer SHA-256
  `41f9aba6eb85bb173827f13cb6b7b1d54b7ea9346faf7c9e5b1af859bbd42ec7`).
  All 18 submitted non-ledger payload hashes verified; four CSV entries and
  their ledger hashes were refreshed after CRLF-to-LF repository
  normalization. Its geometric-uniform information laws, entropy/Fisher,
  dyadic Thue--Morse, inverse-Fabius/Lambert, and q-asymptotic themes place it
  with the broad frontier series. It remains standalone pending
  post-publication claim review, semantic deduplication, experiment
  assessment, and a Lean crosswalk; manuscript labels do not establish Lean
  verification. The filed PDF hard-codes Latin Modern and inherits five
  embedded/subset Type-3 font rows from its vector figures; canonical promotion
  requires a Libertinus/Type-3-free rebuild and refreshed checksums.

- [`Digital_Spectral_Geometry_and_Log_Periodic_Saddles/`](Digital_Spectral_Geometry_and_Log_Periodic_Saddles/),
  *Digital Spectral Geometry and Log-Periodic Saddles: Frontier Results for
  the Thue--Morse, Fabius, Inverse-Fabius, and Rvachev Systems* (24 A4 pp,
  1949 source lines; with a 490-line numerical generator),
  arrived on 2026-08-30 from the rootless archive
  `Fabius_Rvachev_Frontier_Report_Package.zip` (outer SHA-256
  `0028cb4f47134574ba7cd698bfc0ec11f08776b320cbc82b8467bea20d865f6d`).
  The arrival's own manifest covers only its TeX and PDF; the complete ten-file
  arrival ledger is recorded in `ARRIVAL_SHA256SUMS`. The repository repair
  replaces the failed numerical run with captured reproducible output and three
  generated figures, reruns a dated 140-file corpus audit, records the
  paper-versus-Lean boundary, adopts canonical A4/27 mm/Libertinus styling and
  PDF metadata, and rebuilds exactly three passes. All fonts are embedded and
  subset, no Type 3 font or overfull box remains, and the exhaustive 17-entry
  live `SHA256SUMS` verifies. Its zero multiplicities,
  spectral zeta and digit count, log-periodic complex dimensions, endpoint and
  inverse-Fabius saddles, Appell/Strang--Fix reproduction, and integer-base
  generalization substantially overlap Parts II, V, VII, and VIII of the
  consolidated volume below. One conjecture is already false as stated:
  strict log-concavity for every real base `b > 1` is refuted for `b > 2` by
  the canonical exact plateau, and at `b = 2` by the flat mode (equivalently
  `q < 1/2` and `q = 1/2`, respectively), so it is not a live frontier claim.
  A first Lean crosswalk now closes the finite base-`b` scale count and
  digit-recovery arithmetic, including composite bases; the package remains
  standalone while the bundled analytic product/order theorem and the
  remaining report-wide deduplication are still pending.  Manuscript theorem
  labels do not establish Lean proof status.

## Current Lean crosswalk: general-base multiplicity arithmetic

Put

`ν_b(n) = max {h : b^h ∣ n}`, `A_b(N) = ∑_{n=1}^N (1 + ν_b(n))`,

and let `s_b(N)` be the sum of the base-`b` digits of `N`.  When `b` is
composite, `ν_b` is a base-`b` divisibility or scale exponent, not an additive
valuation; for example, `ν_6(2) + ν_6(3) = 0` but `ν_6(6) = 1`.

| Lean declaration | Human-readable statement |
| --- | --- |
| `weightedScaleMultiplicity_const` | In any additive commutative monoid, a constant layer weight `a` gives `W_{b,h ↦ a}(n) = (ν_b(n)+1) • a`. |
| `weightedScaleMultiplicity_one_nat` | For natural-valued unit weights, `W_{b,1}(n) = ν_b(n)+1`. |
| `sum_range_weightedScaleMultiplicity_of_log_lt` | For every integer `b ≥ 2`, every height `H` with `log_b N < H`, and weights in any additive commutative monoid, `∑_{n=1}^N ∑_{h=0}^{ν_b(n)} w_h = ∑_{h=0}^{H-1} ⌊N/b^h⌋ • w_h`. The extra high layers vanish automatically. |
| `sum_range_weightedScaleMultiplicity_log` | For every integer `b ≥ 2`, every `N ≥ 0`, every additive commutative monoid, and every weight sequence `w_h`, `∑_{n=1}^N ∑_{h=0}^{ν_b(n)} w_h = ∑_{h=0}^{⌊log_b N⌋} ⌊N/b^h⌋ • w_h`. This sharpens the older cumulative theorem to the natural logarithmic height. |
| `sum_range_div_pow_log_eq_self_add_tail` | If `L = ⌊log_b N⌋`, then `∑_{h=0}^L ⌊N/b^h⌋ = N + ∑_{i=0}^L ⌊N/b^(i+1)⌋`; the apparent final extra term is zero because `N < b^(L+1)`. |
| `sub_one_mul_sum_padicValNat_succ_add_digitSum` | For every integer `b ≥ 2`, including composite bases, `(b-1)A_b(N) + s_b(N) = bN`, exactly in the naturals and including `N=0`. |
| `sum_range_padicValNat_succ_eq_sub_digitSum_div` | Equivalently, `A_b(N) = (bN-s_b(N))/(b-1)`. |

`BaseDigitMultiplicity.lean` proves the finite count and digit-recovery
arithmetic in equations `base-b-count` and `digit-recovery` once the analytic
zero count `N_b(c_bN)` has independently been identified with `A_b(N)`.  It
does not define `Φ_b`, prove the base-`b` canonical product, or prove that its
zeros have order `1 + ν_b(n)`.  The integer-base zero set is separately
represented by `ReciprocalIntegerGammaZeros.lean`, which does not establish
collision orders.  For real `s > 1`, `SpectralZetaWeighted.lean` proves the
arithmetic Dirichlet-series identity

`∑_{n≥1} (1+ν_b(n))n^(-s) = (∑_{n≥1} n^(-s))/(1-b^(-s))`.

It deliberately leaves the first series in `p`-series form rather than
identifying a complex meromorphic Riemann zeta function.  Thus the manuscript's
bundled base-`b` canonical-product/order theorem, complex spectral-zeta
identity, probabilistic cumulant formula, and log-periodic transseries are not
proved wholesale by this arithmetic module.

- [`Frontier_Directions_for_Fabius_Rvachev_Analysis/`](Frontier_Directions_for_Fabius_Rvachev_Analysis/),
  *Frontier Directions for Fabius--Rvachev Analysis* (33 pp), arrived on
  2026-08-30 from `fabius_frontier_report_bundle-D.zip` (outer SHA-256
  `39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`)
  and was filed under a title-derived collision-safe name rather than its
  generic wrapper. All 34 submitted payload hashes verified; nine CSV entries
  were refreshed after CRLF-to-LF repository normalization. It remains
  standalone pending post-publication assessment, editorial deduplication, and
  a Lean crosswalk; manuscript labels do not establish Lean verification.

The broad multi-topic "collected new results" report series,
consolidated (2026-08-28) into the 272-page single volume
[`Frontier_Compilations/`](Frontier_Compilations/): ten absorbed reports,
displayed as ten outer parts.

- **Report I / displayed Part I** — *Tail Quadrature, Exact Dyadic Error Laws,
  and q-Binomial Acceleration for the Fabius–Rvachev System*
  (formerly `Fabius_Rvachev_Frontier_Report/`);
- **Report II / displayed Part II** — *Arithmetic Spectra of the Rvachev Sinc Product*
  (formerly `Fabius_Rvachev_Frontier_Report-2/`);
- **Report III / displayed Part III** — *Zero-Divisor-Preserving q-Richardson Extrapolation
  for the Fabius–Rvachev Sinc Product*
  (formerly `Fabius_Rvachev_Frontier_Report-3/`);
- **Report IV / displayed Part IV** — *Midpoint Transmutation, Dyadic Cardinal
  Reproduction, and Holonomic Obstructions*
  (formerly `Fabius_Rvachev_Frontier_Report_2026-08-27/`);
- **Report V / displayed Part V** — *Gamma Duality, Total Positivity, and
  Lambert-Localized Moments in the Fabius–Rvachev System*
  (formerly `Fabius_Rvachev_New_Frontiers/`);
- **Report VI / displayed Part VI** — *Confluent Digital Extrapolation and
  Lambert-Phase Tomography in the Fabius–Rvachev System*
  (formerly `fabius_frontier_report_bundle/`);
- **Report VII / displayed Part VII** — *Dyadic Spectral Determinants for the Fabius–Rvachev
  System* (formerly `fabius_frontier_results_bundle/`);
- **Report VIII / displayed Part VIII** — *Logarithmic q-Richardson Acceleration and Lambert
  Phase Locking in Fabius–Rvachev Analysis*
  (formerly `fabius_frontier_new_results/`); its three former internal parts
  are retained as sections: *Exact logarithmic tails and multiplicative q-Richardson acceleration*,
  *Lambert phase-locked extraction of the endpoint oscillation*, and *Unified
  interpretation, formalization path, and research program*;
- **Report IX / displayed Part IX** — *Binary Spectral–Endpoint Bridges for the Fabius and
  Rvachev Functions*
  (formerly `fabius_frontier_spectral_endpoint_report_bundle/`);
- **Report X / displayed Part X** — *Beyond the Dyadic Fabius Web*
  (formerly `beyond_dyadic_fabius_web_report/`).

The mathematical bodies of reports I--IX were preserved modulo their
standalone wrappers and the mechanical prefixing of labels, citation keys,
macro names, and asset paths; wrapper counters, theorem captions, and raster
figure selection were normalized for the consolidated layout. Report X
received the same treatment plus post-snapshot Lean-status updates recording
exact-support, absolute-continuity, and null-singleton results. The former
report directories were deleted. Provenance with SHA-256 hashes is recorded
in the volume itself, and git history is the archive.

Report VIII's logarithmic phase-extraction theorem is now represented
directly in Lean. `FabiusLambertPhaseLockedPullback.lean` transports the
arbitrary-order endpoint remainder to the exact Lambert nodes,
`CompleteHomogeneousAsymptotics.lean` and
`LambertReciprocalAsymptotics.lean` control the residual alphabet and growing
row, and `FabiusLambertPhaseExtraction.lean` proves the fixed-order finite
Poincaré hierarchy and integer-phase-ray convergence.
`CompleteHomogeneousBell.lean` proves the generic finite-alphabet Bell
conversion, `LambertPhaseLockedBell.lean` specializes it to shifted
reciprocal power sums and both exact moment forms, and
`FabiusLambertPhaseExtractionBell.lean` rewrites each residual term and every
finite residual partial sum in Bell form. The normalized specialization uses
the rational-algebra/characteristic-zero field layer; total field inversion
still requires no positivity or nonzero-shift premise. Thus the finite
complete-homogeneous/Bell/generalized-harmonic conversion is closed. These
identities do not prove convergence of the infinite residual series or add a
new asymptotic estimate. The infinite residual convergence problem,
exponentiated/multiplicative Bell relative-error hierarchy, higher derivative
extractors, sign/bracketing claims, and growing-order uniformity remain open.

Post-snapshot Lean status began at source checkpoint `b3720d4b5` with two
generic finite-algebra modules relevant to Report I; the current tree adds the
generic Jacobi layer and its exact up-measure comparison:

- `FiniteMomentGram.lean` exports `momentFunctional`,
  `momentFunctional_apply`, `momentFunctional_monomial`,
  `momentFunctional_C`, `momentFunctional_X_pow`,
  `momentFunctional_of_linearMap`, `momentFunctional_injective`,
  `momentFunctional_eq_sum_support`, `momentFunctional_eq_sum_range`,
  `momentFunctional_map`, `momentPairing`, `momentPairing_apply`,
  `momentPairing_monomial`, `momentPairing_X_pow`,
  `momentPairing_isSymm`, `momentHankelMatrix`,
  `momentHankelMatrix_apply`, `momentHankelMatrix_transpose`,
  `momentHankelMatrix_succ_submatrix`, `momentHankelMatrix_map`,
  `momentHankelDet`, `momentHankelDet_zero`, `map_momentHankelDet`,
  `finiteMomentPairing`, `finiteMomentPairing_toMatrix`, and
  `finiteMomentPairing_nondegenerate_iff`.
- `GramStieltjes.lean` exports `gramStieltjesNumerator`,
  `gramStieltjesNumerator_coeff`, `gramStieltjesNumerator_natDegree_le`,
  `momentPairing_gramStieltjesNumerator_X_pow_eq_zero`,
  `momentPairing_gramStieltjesNumerator_X_pow_eq_det`,
  `gramStieltjesNumerator_coeff_top`,
  `momentPairing_gramStieltjesNumerator_eq_coeff_mul_det`,
  `momentPairing_gramStieltjesNumerator_self`,
  `gramStieltjesPolynomial`, `gramStieltjesPolynomial_natDegree_le`,
  `gramStieltjesPolynomial_coeff_top`,
  `gramStieltjesPolynomial_isMonicOfDegree`,
  `momentPairing_gramStieltjesPolynomial_X_pow_eq_zero`,
  `momentPairing_gramStieltjesPolynomial_eq_zero`,
  `eq_gramStieltjesPolynomial_of_isMonicOfDegree_of_orthogonal`,
  `momentPairing_gramStieltjesPolynomial_self`, and
  `momentPairing_gramStieltjesPolynomial_self_ne_zero`.
- `FiniteMomentJacobi.lean` adds `momentPairing_X_mul_left`,
  `momentPairing_eq_zero_of_forall_X_pow`, `gramStieltjesNorm`,
  `momentPairing_gramStieltjesPolynomial_X_pow_eq_norm`,
  `momentPairing_gramStieltjesPolynomial_self_eq_norm`,
  `gramStieltjesNorm_ne_zero`, `gramStieltjesJacobiDiagonal`,
  `gramStieltjesJacobiSubdiagonal`,
  `gramStieltjesJacobiSubdiagonal_eq_det_ratio`,
  `gramStieltjesPolynomial_three_term_zero`, and
  `gramStieltjesPolynomial_three_term`.
- `OrthogonalPolynomialGramBridge.lean` adds
  `momentFunctional_upMoment_eq_integral`,
  `momentPairing_upMoment_eq_integral`,
  `momentHankel_eq_momentHankelMatrix`,
  `hankelDet_eq_momentHankelDet`,
  `hankelOrthoPolynomial_eq_gramStieltjesNumerator`, and
  `upOrthoPolynomial_eq_gramStieltjesPolynomial`, together with
  `hankelRatio_eq_gramStieltjesNorm`,
  `gramStieltjesJacobiDiagonal_upMoment_eq_zero`, and
  `gramStieltjesJacobiSubdiagonal_upMoment_eq` for the recurrence data.

This is a finite, generic Gram--Stieltjes layer under nonzero-Hankel-minor
hypotheses; the first three modules themselves assume no measure and prove no
positivity.  The bridge identifies their objects exactly with the
up-measure-specific matrix, determinant, determinant polynomial, and monic
normalization.  The complementary Fabius-specific modules
`MomentHankelMatrix.lean`, `MomentHankelValues.lean`, and
`OrthogonalPolynomial*.lean` prove positivity and nonvanishing, the monic
orthogonal construction, parity, the symmetric three-term recurrence, and the
first exact Jacobi data.  Root location or simplicity, Gaussian/Lobatto
quadrature, finite or infinite Jacobi/Stieltjes-fraction identification, and
convergence remain open.  This status update does not alter the absorbed
reports or their recorded provenance hashes.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
