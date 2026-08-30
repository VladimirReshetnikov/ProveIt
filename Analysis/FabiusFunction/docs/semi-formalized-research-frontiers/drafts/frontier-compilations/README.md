# Frontier compilations

The Digital Spectral Geometry intake is registered once, in the
[`spectra-and-arithmetic`](../spectra-and-arithmetic/) group.  That filing
preserves the full verified arrival ledger, repairs the failed audit and
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
Its submitted 34-row ledger was verified and is preserved as
`ARRIVAL_SHA256SUMS`; the normalized 36-row current ledger passes in full.
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
Poincaré hierarchy and integer-phase-ray convergence. The report's
Bell/generalized-harmonic conversion, exponentiated Bell hierarchy, higher
derivative extractors, sign/bracketing claims, and growing-order uniformity
remain open.

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
