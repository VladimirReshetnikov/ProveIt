# Frontier compilations

> **Source-only merge status (2026-08-31).** Canonical-notation edits changed
> the consolidated `Frontier_Compilations.tex`, but the retained 274-page PDF
> was not rebuilt. Its previous page, font, and build facts are historical
> validation facts rather than a synchronization claim; recompilation and any
> dependent metadata refresh are deferred.

The Digital Spectral Geometry intake is registered once, in the
[`spectra-and-arithmetic`](../spectra-and-arithmetic/) group.  That filing
records verification of the full arrival ledger, which is recoverable from
Git history, repairs the failed audit and
numerical generation, corrects the false curvature claim, and supplies the
policy-conforming canonical build; the unrepaired duplicate formerly listed
here has been removed.

New standalone intake members:

The standalone
[`Geometric_Uniform_Frontier_Directions/`](Geometric_Uniform_Frontier_Directions/)
package, *Frontier Directions for Fabius--Rvachev Analysis*, was filed on
2026-08-30 from `fabius_frontier_report_bundle-D.zip` (1,508,514 bytes;
SHA-256
`39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`).
Its submitted 34-row ledger was verified at intake and remains recoverable
from Git history; a later normalized 36-row ledger also passed before
checksum ledgers were retired.
The 1,641-line report and 874-line deterministic experiment suite were
replayed, audited, normalized to the shared A4/27 mm/Libertinus style, and
rebuilt as a 30-page PDF with embedded/subset fonts and no Type 3.  Exact
tables reproduced; the three floating-point tables exhibit only documented
last-place platform drift.  The report is paper-level: current Lean already
covers the geometric-uniform law, its positive-parameter density and
convolution interfaces, weighted sinc--zeta expansions, and the fixed
half--quarter split, but not the report's negative-parameter duality,
all-parameter asymptotics, exact subdyadic derivative norms, arbitrary-base
spectral divisor, Legendre scaling, or periodic Laplace phase.  Its spectral
and reciprocal-integer directions conceptually overlap the separately
audited packages, without wholesale textual duplication.

- [`Geometric_Uniform_Convolutions_and_New_Frontiers/`](Geometric_Uniform_Convolutions_and_New_Frontiers/),
  *Geometric Uniform Convolutions and New Frontiers around the
  Fabius--Rvachev System*, is the title-derived filing of the generic
  source-only wrapper `drafts/incoming/fabius-frontier-report-H/`, committed
  directly by `8a184546747082cbd92ad4675fb61981c6b8c3b6`.  The incomplete
  delivery consists of one 1,656-line LF TeX manuscript: no PDF, README,
  external code, data, figures, captured output, checksum file, repository
  metadata, or archive was supplied.  Intake repaired three form-feed-corrupted
  `\frac` tokens and added a repository-generated one-entry checksum ledger,
  now retired but recoverable from Git history.  The
  package still has no PDF, and the source has not yet been shown to compile.

  Its q-deformed derivative formulas, Gaussian/Edgeworth layer,
  valuation-weighted zeros, non-Gevrey growth, and periodic Lambert endpoint
  program overlap several same-batch reports and the consolidated corpus; its
  abstract also says reproducible Python code accompanies the report, but none
  was delivered.  The source remains standalone pending post-publication compilation,
  claim-by-claim comparison, and a Lean crosswalk.  Nothing in the intake
  establishes that any manuscript theorem is proved in Lean.

The broad multi-topic "collected new results" report series,
consolidated (2026-08-28) into the retained 274-page single volume
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
in the volume itself, and git history is the archive.  Bibliographic links to
the retired Fourier-decay audit volumes are pinned to their immutable
pre-consolidation snapshot; the live Fourier-decay corpus is the single
canonical volume registered in the `rvachev_up_fourier_decay` group.

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

## Activation, sinc, and CDF status freeze

The post-snapshot activation tranche is a separate real, totalized hyperbolic
kernel, not a complex-sinc identification.  At source checkpoint
`a345425d21d90e680bf15e34093af42c69c08a83`, its seven modules expose six
definitions and 99 theorems: the totalized activation dictionary, the finite
Taylor jet, the arbitrary-index square-summable budget and sharp Tannery limit,
and the geometric/dyadic effective-dimension bounds and asymptotics.  The local
coefficient is `activationProbability x / x^2 -> 1/3`, and the geometric
coefficient is `(1-q)/(3*(1+q))` for `|q| < 1`.  Negative `q` is included in
these deterministic identities; the report's positive-weight active-count
interpretation is restricted to `0 < q < 1`, with no Bernoulli-family or
expectation bridge asserted.

The sinc union is now exact at both levels: the four product declarations in
`GeometricReciprocalGamma.lean` give locally uniform complex product
convergence, genuine `Multipliable`/`HasProd` witnesses, and entire-ness for
`|q| < 1`; the two declarations in
`GeometricSincCharacteristicFunction.lean` identify the real geometric-law
characteristic function with the phase-bearing rescaled product and the paired
geometric reciprocal-Gamma product, including `q = 0` and negative `q`.  A
centered wrapper and compact-uniform convergence of the full phase-bearing
prefixes remain open.

The CDF union is parameter-scoped.  `GeometricUniformCDF.lean` has 31 public
declarations: its CDF definition and basic order/measurability facts are total
in real `q`; continuity, reflection, and midpoint use `|q| < 1`; exterior tails
use `0 <= q < 1`; and conditioning, the classical nonnegative density,
Radon--Nikodym identity, compact support, and `C^infty` regularity use
`0 < q < 1`.  The nonpositive diagnostics show that the selected totalized
density is zero or nonpositive and its clamped `withDensity` measure is zero,
so the paper-level corrected signed-density construction remains open, even
though fixed-point uniqueness for the probability law is proved for every
`|q| < 1`.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
