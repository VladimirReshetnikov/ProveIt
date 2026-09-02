# Exponents and q-series

The seven live document packages are organized by their primary mathematical
overlap:

- [`q_pochhammer_q_binomial_monograph/`](q_pochhammer_q_binomial_monograph/)
  is the single canonical synthesis of forward q-series and branch-aware
  inverse-q theory.
- [`q-fabius-parameter-deformations/`](q-fabius-parameter-deformations/)
  contains the continuous-parameter, limit-regime, susceptibility, and smooth
  response reports for the geometric q-Fabius family.
- [`geometric-sinc-and-exponent-families/`](geometric-sinc-and-exponent-families/)
  contains the central exponent/geometric-sinc synthesis and its
  negative/reciprocal and cyclotomic companion reports.

The former `q-pochhammer-and-inversion/` locations are recorded in pinned
history; no live index or package remains at that path. Every live package
appears exactly once. The former three
general-q-series guides, forward q-Pochhammer/q-binomial monograph, and
inverse-q synthesis have been dispositioned into
[`q_pochhammer_q_binomial_monograph/`](q_pochhammer_q_binomial_monograph/).
Their earlier names, arrival hashes, and publication facts remain provenance,
not parallel live documents. The current canonical TeX postdates its retained
historical PDF; the exact source and artifact receipt appears once in the
detailed package record below. Its crosswalk preserves the generic
`QPochhammerInfinite.lean` and `QPochhammerDissection.lean` layers, the
five-theorem `QPochhammerEntire.lean`, the three-theorem outer-product
normal-convergence leaf, the six-theorem exponent-identifiability leaf, the
earlier 69-declaration q-series tranche, and the five `6c7a69be9` modules
contributing 50 declarations. The newest basic-hypergeometric, Heine,
q-Gauss, infinite-bound, and complex-order modules contribute 26 declarations
(five definitions and 21 theorems); `QMultinomial.lean` contributes one
definition and nine theorems, including the empty- and singleton-list boundary
cases. The final eight-module q-calculus/theta tranche contributes five
definitions and 53 theorems across `GaussianBinomialPalindromic.lean`,
`JacksonIntegral.lean`, `QExponential.lean`, `ThetaQuasiPeriodicity.lean`,
`JacobiCubic.lean`, `QPochhammerLogDerivative.lean`,
`QPochhammerOrderDerivative.lean`, and
`GaussianBinomialPolynomialStructure.lean`. The next source-only extension is
`CentralQBinomialReduction.lean` (0+6) together with
`CyclotomicFactorization.lean` (0+7). The latest extension adds
`PrimitiveRootBlock.lean` (0+3), `QLucas.lean` (0+8),
`CyclotomicDivisibility.lean` (0+3), `QCatalan.lean` (1+11),
`NewtonInterpolation.lean` (2+13), and `QBetaIntegral.lean` (1+8): four
definitions and 46 theorems. A fresh three-pass render and ledger refresh are
pending. Retained PDFs under its `assets/` tree are research
figures, not alternate manuscript renderings. The current Lean audit contains
exactly 665 facade-reachable modules and 8,819 public declarations, with no
missing module headers or declaration documentation.

## Detailed package record

Current packages and retained intake records:

- [`fabius_q_frontiers_report/`](q-fabius-parameter-deformations/fabius_q_frontiers_report/),
  *Parameter-Flow, Gaussian, and Large-Deviation Frontiers for the
  q-Fabius--Rvachev Family* (23 A4 pp and 1,506 source lines at arrival;
  current main artifact: 22 A4 pp from 1,492 source lines; with two scripts,
  four CSV tables, two captured outputs, and four PDF/PNG figure pairs),
  arrived as a bare directory in direct-arrival commit
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`; no archive or outer hash was
  supplied. Its submitted ledger covers all 20 non-ledger payloads and was
  refreshed after four CSV entries received CRLF-to-LF normalization. The
  later strict rebuild replaced the main TeX/PDF pair; the refreshed 20-entry
  operational ledger verifies every current payload. All five current PDFs
  are readable and unencrypted (26 pages total). The main report has 33
  embedded/subset font rows, including five Libertinus rows and eight Type-3
  rows inherited from the four included vector figures; the standalone figure
  PDFs contain the same eight Type-3 rows. Figure-font normalization remains
  deferred.

- [`Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/`](q-fabius-parameter-deformations/Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/),
  *Continuous-Parameter Edgeworth Theory, Large Deviations, and Quadratic
  q-Gevrey Regularity at the Fabius--Rvachev Frontier* (29 A4 pp and 1,387
  main-source lines at arrival; current main artifact: 29 A4 pp from 1,372
  source lines, SHA-256
  `e9d99619992f78050326249272b18f5941f659dea0f022522b23ec218953d5bf`),
  arrived on 2026-08-30 in direct-arrival commit
  `52179f63fe955a64508915eedaa560de9f3056da` under the bare generic wrapper
  `Fabius_Rvachev_Frontier_Report_2026-08-30-G/` and was filed under this
  title-derived collision-safe name. Its manifest covers the full delivery.
  The current PDF was rebuilt from the final source in three strict passes;
  the refreshed 19-entry ledger verifies every current payload. The main PDF
  has 33 embedded/subset font rows, including six Libertinus rows and six
  Type-3 rows inherited from the three included vector figures; the standalone
  figure PDFs contain the same six Type-3 rows. Its title and abstract concern
  continuous-parameter Edgeworth and deviation regimes, Lambert endpoint
  asymptotics, and quadratic-exponential Denjoy--Carleman regularity.

- [`q_pochhammer_q_binomial_monograph/`](q_pochhammer_q_binomial_monograph/),
  *q-Series and Inverse q-Analogs: A Proof-Oriented Synthesis*, is the one
  canonical source publication for this subgroup. The merged master has 28
  numbered forward chapters, including four chapters distilled from the three
  general guides; the former inverse-q synthesis contributes eight numbered
  branch-aware chapters and one inverse-source provenance appendix. Repeated
  results are stated once in their strongest proved form, while independent or
  genuinely stronger results are retained with complete human-readable proofs.
  Its
  [`PROVENANCE.md`](q_pochhammer_q_binomial_monograph/PROVENANCE.md)
  records the five-publication merge surface and the earlier six-package
  inverse lineage. The completed
  [`source_concordance.csv`](q_pochhammer_q_binomial_monograph/source_concordance.csv)
  gives a reviewed disposition for all 547 source result environments from the
  five merged publications. Its canonical destinations comprise 73 Lean-proved
  rows, 405 human-proved
  frontier results, 60 not-applicable rows, and 9 conjectures. The historical
  [`theorem_concordance.csv`](q_pochhammer_q_binomial_monograph/theorem_concordance.csv)
  continues to account for all 260 inverse-source result environments, and
  [`assets/ASSET_DISPOSITION.csv`](q_pochhammer_q_binomial_monograph/assets/ASSET_DISPOSITION.csv)
  preserves the 77-row decision record for unique scripts, data, outputs, and
  figures. Pinned source revisions and Git history preserve every superseded
  layout and arrival fact.

  The earlier 335-, 340-, 345-, 347-, and 348-page synchronized pairs remain
  historical provenance. The retained
  `q_pochhammer_q_binomial_monograph.pdf` is the validated pre-aed 357-page A4
  artifact, with SHA-256
  `3673b2cb7d617ccbcc9e3c32af17dbb9f4e8d8c16882d889d2a299bd128e0593`.
  Its A4 boxes, text extraction, embedded/subset Type-1 fonts including
  Libertinus, absence of Type-3 fonts, and targeted visual review passed at
  that checkpoint. The current TeX is newer and includes the generic
  infinite/dissection API, five compatibility wrappers, outer normal
  convergence, exponent identifiability, the complete q-series/q-calculus
  union, and the central-reduction and cyclotomic-factorization modules. That
  PDF validates the preceding 659-module/8,769-declaration source and omits
  the latest six-module/fifty-declaration extension.
  Consequently the source and retained PDF are distinct payloads and no render
  parity is claimed. The current source fingerprint is intentionally deferred
  until the pending final-source build and ledger refresh. PDF files retained
  beneath `assets/` are vector research figures, not manuscript builds.
  Manuscript result labels and numerical checks remain
  distinct from Lean verification.

- [`Cyclotomic_q_Fabius_Rvachev_Frontier/`](geometric-sinc-and-exponent-families/Cyclotomic_q_Fabius_Rvachev_Frontier/),
  *Cyclotomic Blow-Ups and Natural Boundaries for the q-Fabius--Rvachev Sinc
  Product* (25 pp at arrival; currently 28 A4 pp and 1,875 source lines),
  arrived on 2026-08-30 from
  `Cyclotomic_q_Fabius_Rvachev_Frontier.zip` (outer SHA-256
  `029da7d9ec96a0b2e5c4164c37f2b361dd015112bd0c6237263e3c538c5b0f64`).
  All 22 submitted payload hashes verified; five CSV entries were refreshed
  after CRLF-to-LF repository normalization. Its title and abstract place its
  radial root-of-unity expansions, claimed natural-boundary theorem,
  cyclotomic blow-ups, Bell/moment condensation, and inverse branches beside
  the consolidated q-series frontier. A post-publication revision crosswalks
  the global geometric-sinc q-Pochhammer factorization while leaving the
  cyclotomic asymptotic and natural-boundary layers manuscript-only. The
  retained main PDF has 28 A4 pages, so the five PDFs have 32 pages in total
  (28 main plus four one-page figures). Its current 1,875-line source postdates
  that rendering; a fresh strict three-pass build and operational-ledger
  refresh are pending. The retained main PDF uses
  embedded/subset Type-1 Libertinus fonts with no Type 3 font; the unchanged
  standalone vector figures retain nine embedded/subset Type-3 rows as
  disclosed archival debt.

- [`Fabius_Rvachev_Frontier_Report/`](geometric-sinc-and-exponent-families/Fabius_Rvachev_Frontier_Report/),
*Negative Parameters, Reciprocal Bases, and the Gaussian Boundary* (current
1,475-line source and matching 26-page A4 PDF), arrived on 2026-08-30 with all
13 payload checksums verified. Its current PDF was rebuilt from the final
source, and the refreshed operational ledger verifies all thirteen current
payloads. It develops
negative-parameter affine transport, reciprocal-base digit reversal,
multisection, shape theory, and the Gaussian boundary for geometric-uniform
laws.  Because much of that subject already appears in Part VII of the
consolidated volume, the report remains standalone until its genuinely new
claims are isolated and the overlap is deliberately deduplicated.  Paper
theorem labels do not by themselves assert Lean formalization.

- [`Fabius_Flat_Parameter_Response_Dynamics/`](q-fabius-parameter-deformations/Fabius_Flat_Parameter_Response_Dynamics/),
  *Flat Parameter Fronts, q-Susceptibility, and Smooth Dynamics* (26 A4 pp;
  current 1,890-line TeX and 519-line deterministic exact/Monte-Carlo program),
  was filed on 2026-08-30 from `fabius_frontier_report_2026.zip` (803,598 bytes;
  SHA-256
  `afdcf522589a7baad82c81a527c02dcc09e58455ab14c57a9c492e65563c647e`).
  Its immutable 13-entry arrival ledger verifies 13/13. The current PDF was
  rebuilt from the final source, and the refreshed 17-entry operational ledger
  verifies 17/17. The pinned replay reproduced the two exact
  algebra tables, common-random-number table, and two figures byte-for-byte;
  the two Monte-Carlo tables differed only at documented last-bit levels far
  below their sampling errors. A hostile review repaired the conditional-law
  quantifier in the velocity theorem, the KR basepoint argument, endpoint and
  orbit hypotheses, and the false small-divisor expression. Higher-response
  resolvents now require a finite zero-mass representing measure, while the
  all-orders Koenigs/dynamical layer is explicitly conditional on hypothesis
  (K); none of the new parameter-response claims is asserted as an exact Lean
  theorem. The canonical A4/27 mm/Libertinus PDF was rebuilt in exactly three
  strict passes with every font embedded/subset and no Type 3 fonts.

Generalizations of the dyadic construction to arbitrary exponent
sequences and the q-series calculus that organizes them: the
exponent-sequence convolution monoid with its Newton-basis frontiers, and
q-binomial Richardson acceleration of geometric sinc products. The
denominator-free Gaussian/q-binomial core used by both is formalized at arbitrary
ratio. `QBinomialCauchy.lean` exhaustively supplies one definition and five
theorems: the finite q-Cauchy identity and its compatibility spelling, its reflected strengthening, the
denominator-free q-Bernstein basis and its partition of unity, and the second
finite Cauchy identity. They hold for arbitrary parameters and degrees over
every commutative ring, including `q = 0`, roots of unity, and zero divisors.
`SymmetricFunctionOrthogonality.lean` exhaustively supplies one definition and
six theorems: evaluated elementary symmetric functions, their Mathlib bridge,
zero-degree and reindexing laws, `Option` and `Fin` weighted-Pascal recurrences,
and the total elementary--complete orthogonality convolution. The structural
API is valid over commutative semirings; orthogonality is valid over every
commutative ring, including the empty family and degree zero. Together with the
existing `completeHomogeneousEval_option_succ`, the elementary `Option`
recurrence gives both weighted-Pascal laws exactly.

`FiniteTriangularTransform.lean` has the exhaustive one-definition,
one-theorem surface `lowerTriangularTransform` and
`lowerTriangularTransform_comp`. For `[Semiring R] [AddCommMonoid M]
[Module R M]`, a total ordered kernel convolution on `Icc j n` yields an
equality of whole sequence functions; no commutativity of `R`, subtraction,
topology, or infinite summability is used.

`SymmetricFunctionTransform.lean` has the exhaustive four-definition,
five-theorem surface `completeHomogeneousKernel`, `signedElementaryKernel`,
`completeHomogeneousKernel_left_orthogonality`,
`completeHomogeneousKernel_right_orthogonality`,
`completeHomogeneousTransform`, `signedElementaryTransform`,
`signedElementaryTransform_completeHomogeneousTransform`,
`completeHomogeneousTransform_signedElementaryTransform`, and
`weightedSymmetricFunction_inversion`. The complete-homogeneous kernel and
transform need only a commutative semiring. The signed declarations and all
inverse results use a commutative ring; transform targets need only an
additive commutative monoid with its module structure. Both kernels are
zero-extended above the diagonal, and both whole-function compositions reuse
the generic triangular theorem. Thus weighted inversion is exact, with a
module-valued strengthening.

`SymmetricFunctionGenerating.lean` has the exhaustive two-definition,
six-theorem surface `elementarySymmetricGeneratingSeries`,
`completeHomogeneousGeneratingSeries`,
`coeff_elementarySymmetricGeneratingSeries`,
`coeff_completeHomogeneousGeneratingSeries`,
`elementarySymmetricGeneratingSeries_eq_prod`,
`elementarySymmetricGeneratingSeries_neg_mul_completeHomogeneousGeneratingSeries`,
`completeHomogeneousGeneratingSeries_eq_invOfUnit_elementarySymmetricGeneratingSeries_neg`,
and `prod_one_sub_qPow_X_mul_gaussianBinomialGeneratingSeries`. The
definitions, coefficient results, and finite elementary product hold over a
commutative semiring; reciprocity, canonical inversion, and the finite
Gaussian reciprocal identity require a commutative ring. These close only
the formal-power-series halves of the weighted-generating and reciprocal
finite claims. Analytic evaluation and convergence under `|w_i z| < 1` or
`|z| < 1` remain open.

The complementary finite-index API in `CompleteHomogeneousGenerating.lean`
has one definition and six theorems:
`completeHomogeneousGeneratingSeriesOn`,
`coeff_completeHomogeneousGeneratingSeriesOn`,
`completeHomogeneousGeneratingSeriesOn_empty`,
`completeHomogeneousGeneratingSeriesOn_insert`,
`one_sub_mul_completeHomogeneousGeneratingSeriesOn_insert`,
`prod_one_sub_mul_completeHomogeneousGeneratingSeriesOn`, and
`completeHomogeneousGeneratingSeriesOn_eq_invOfUnit_prod`. Its coefficient,
empty-family, and adjoining-variable results hold over commutative semirings;
its denominator-clearing and canonical-inverse results hold over arbitrary
commutative rings, including rings with zero divisors. Together, this API and
`SymmetricFunctionGenerating.lean` prove both formal algebraic halves of the
weighted generating-product theorem, but neither proves its analytic clause.
Separately, the sole public theorem
`completeHomogeneousEvalOn_isBigO_pow` in
`CompleteHomogeneousAsymptotics.lean` transfers coordinatewise `O(g)` bounds
through every fixed complete homogeneous degree to `O(g^n)`, including degree
zero and without a nonvanishing hypothesis on `g`; it does not evaluate or
prove convergence of either formal series.

`BitPositionQBinomial.lean` gives both the zero-based and literal
one-based weighted-subset enumerations. `QBinomialInversion.lean` proves the
Gaussian chain law, general alternating rows, and both finite convolution
orders for unscaled and independently scaled kernels; the scale is arbitrary
and need not be invertible. In `QBinomialTransform.lean`, the two forward
definitions require `[Semiring R] [AddCommMonoid M] [Module R M]`, the two
signed inverse definitions require `[Ring R]` with the same target
assumptions, and all four theorems require `[CommRing R]` with that additive
commutative monoid target. Both compositions are whole-function equalities,
the inversion statements are exact iff results, and the refactored proofs
reuse `lowerTriangularTransform_comp`; Gaussian kernels are zero-extended
above the row. Its exhaustive four-definition, four-theorem surface is
`scaledGaussianBinomialTransform`, `scaledGaussianBinomialInverseTransform`,
`scaledGaussianBinomialInverseTransform_transform`,
`scaledGaussianBinomialTransform_inverseTransform`,
`scaledGaussianBinomial_inversion`, `gaussianBinomialTransform`,
`gaussianBinomialInverseTransform`, and `gaussianBinomial_inversion`.

`QDifferenceAnnihilation.lean` has the exhaustive four-theorem surface
`sum_scaledGaussianBinomialInverseKernel_mul_pow`,
`sum_gaussianBinomialInverseKernel_mul_geometric_pow`,
`qDifference_sum_eval₂_eq_map_coeff_mul`, and
`qDifference_sum_eval₂_eq_zero_of_degree_lt`. Over every commutative ring,
the scaled signed row has characteristic polynomial
`sum_(k=0)^n (-s)^(n-k) q^(choose (n-k) 2) [n choose k]_q z^k = prod_(j<n) (z-s q^j)`.
With `s = 1` and `z = q^d`, its exact monomial moment
is `prod_(j<n) (q^d-q^j)`, hence is zero whenever `d < n`. More generally,
for a polynomial over any semiring and any scalar-extension homomorphism into
a commutative ring, the row in degree at most `n` extracts the mapped
coefficient of degree `n` times `prod_(j<n) (q^n-q^j)`; it annihilates every
polynomial of degree strictly below `n`. These results include `n = 0` and the
zero polynomial, allow repeated nodes and a zero surviving product, and use no
division, nonzero or invertible base, domain, characteristic, topology, or
convergence hypothesis.

The global identity
`geometricQBinomialWeightNumerator_eq_scaledGaussianBinomialInverseKernel`
is now owned by `GeometricQBinomialLagrange.lean`: it identifies the
denominator-free geometric numerator with the scaled inverse kernel at base
and scale `q` for all natural indices, including above the diagonal. It is
the `s = q` specialization of the preceding characteristic polynomial.
`QBinomialInversionSpecializations.lean` now has exactly two definitions and
four theorems: `qGaussianResidualCoeff`,
`qGaussianReconstructionCoeff`, `qGaussianResidualCoeff_eq`,
`qGaussianReconstructionCoeff_eq`,
`qGaussianReconstructionCoeff_residualCoeff_delta`, and
`qGaussianResidualCoeff_reconstructionCoeff_delta`. These prove both
q-Gaussian coefficient inversions at base `q^2`, scale `-q`. The two
definitions and their pointwise closed-form theorems require only `[Ring R]`;
exactly the two convolution-delta theorems require `[CommRing R]`.

The current geometric q-layer has the following exhaustive public surfaces:

- `GeometricCompleteHomogeneous.lean` has six theorems:
  `completeHomogeneousEval_geometric`,
  `completeHomogeneousEval_scaled_geometric`,
  `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial`,
  `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial_degree`,
  `gaussianBinomial_add_symm`, and
  `gaussianBinomial_symm_via_completeHomogeneous`. They prove both orientations
  of the denominator-free principal specialization, its range and common-scale
  forms, and two Gaussian symmetry laws over every commutative semiring.

- `GeometricLagrangeCompleteHomogeneous.lean` has five theorems:
  `completeHomogeneousEvalOn_geometric_range`,
  `sum_geometricLagrangeWeight_mul_pow_succ_add_eq_gaussianBinomial`,
  `geometricLagrangeQMoment_eq_residual_gaussianBinomial`,
  `completeHomogeneousEvalOn_geometric_range_eq_qBinomial`, and
  `geometricLagrangeQMoment_eq_residual_qBinomial_via_completeHomogeneous`.
  The first is a commutative-semiring alias; the field residual uses finite-node
  injectivity; the rational quotient bridges keep their explicit
  nonzero-Pochhammer or `0 < q < 1` assumptions.

- `GeometricLagrangeQMoments.lean` has one definition,
  `geometricLagrangeQMoment`, and 37 theorems:
  `geometricLagrangeQMoment_eq_weightPolynomial_eval`,
  `geometricLagrangeQMoment_eq_forwardRichardson_eval`,
  `geometricRootPolynomial_inv_eval_pow_mul_signedPowers`,
  `geometricRootPolynomial_inv_eval_pow_mul_triangular`,
  `geometricRootPolynomial_inv_eval_one_mul_triangular`,
  `geometricLagrangeQMoment_eq_qPochhammer`,
  `geometricLagrangeQMoment_zero`, `geometricLagrangeQMoment_eq_zero`,
  `geometricRootPolynomial_inv_eval_pow_eq_qPochhammer_of_le`,
  `geometricLagrangeQMoment_eq_residual_qPochhammer`,
  `qPochhammer_self_add`, `qPochhammer_self_pos_of_pos_of_lt_one`,
  `qBinomial_pos_of_pos_of_lt_one`,
  `gaussianBinomial_eq_qBinomial_of_pos_of_lt_one`,
  `qPochhammer_pow_pos_of_pos_of_lt_one`,
  `qPochhammer_tail_div_self_eq_qBinomial`,
  `geometricLagrangeQMoment_eq_residual_qBinomial`,
  `geometricLagrangeQMoment_firstUncancelled`,
  `negOnePow_mul_geometricLagrangeQMoment_eq_positiveResidual`,
  `negOnePow_mul_geometricLagrangeQMoment_pos`, `qPochhammer_self_succ`,
  `qBinomial_succ_succ_of_pos_of_lt_one'`,
  `qBinomial_succ_succ_of_pos_of_lt_one`,
  `qBinomial_theorem_of_pos_of_lt_one`,
  `sum_qBinomial_triangular_succ_eq_neg_qPochhammer`,
  `abs_geometricLagrangeWeight_eq_qBinomial`,
  `abs_geometricLagrangeWeight_eq_sign_mul`,
  `abs_geometricLagrangeWeight_complement_eq_qBinomial`,
  `sum_abs_geometricLagrangeWeight_eq_qPochhammer_ratio`,
  `neg_qPochhammer_div_self_eq_prod`,
  `sum_abs_geometricLagrangeWeight_eq_prod`,
  `quarterGeometricLagrangeQMoment_eq_qPochhammer`,
  `quarterGeometricLagrangeQMoment_eq_zero`,
  `quarterGeometricLagrangeQMoment_eq_residual_qPochhammer`,
  `quarterGeometricLagrangeQMoment_eq_residual_qBinomial`,
  `quarterGeometricLagrangeQMoment_firstUncancelled`, and
  `sum_abs_quarterGeometricLagrangeWeight_eq_qPochhammer_ratio`. These are
  finite rational identities. Quotient results retain their stated nonzero
  denominators; positivity, sign, and absolute-value formulas retain
  `0 < q < 1`; no analytic convergence or error estimate is claimed.

- `FinitePolynomialFilterExactness.lean` has five theorems:
  `polynomialFilter_response_eq`, `polynomialFilter_exact`,
  `normalizedGeometricRootPolynomial_filter_exact`,
  `forwardGeometricRichardsonPolynomial_filter_exact`, and
  `forwardGeometricRichardsonPolynomial_filter_firstUncancelled`. The generic
  response and mass-one/root laws hold over commutative semirings. The
  geometric field forms retain their nonzero-base and normalization-denominator
  assumptions, cancel the prescribed modes, and expose the first survivor.

- `QuarterCatalanGerm.lean` has two definitions,
  `quarterCatalanCoefficient` and `quarterCatalanGermSeries`, and thirteen
  theorems: `quarterCatalanCoefficient_zero`,
  `quarterCatalanCoefficient_succ_eq_report`,
  `quarterCatalanGermSeries_coeff`, `quarterCatalanGermSeries_coeff_succ`,
  `quarterCatalanGermSeries_constantCoeff`,
  `quarterCatalanGermSeries_equation`,
  `powerSeries_quadratic_injectiveOn_zeroConstant`,
  `eq_quarterCatalanGermSeries_of_equation`,
  `existsUnique_quarterCatalanGermSeries`,
  `dyadicGermTwo_functionalEquation`,
  `rescale_dyadicGermTwo_eq_quadraticInverse`,
  `dyadicGermTwo_eq_rescale_quadraticInverse`, and
  `coeff_dyadicGermTwo_succ`. They give the unique zero-constant solution of
  `D + 4D^2 = (4/9)X` in `ℚ[[X]]`, all of its report coefficients, and the
  exact rescaling bridge to the distinguished dyadic germ and the inverse of
  `X + 4X^2`.

- `FabiusInverseQuarterJet.lean` has exactly two public theorems,
  `iteratedDeriv_centeredFabiusInv_quarter_eq_quadraticInverse` and
  `iteratedDeriv_fabiusInv_five_seventy_two_succ`. They identify the complete
  smooth derivative jet of the actual inverse at `5/72 = F(1/4)` with the
  factorial-scaled quadratic-inverse coefficients and prove
  `G^(m+1)(5/72) = (m+1)! (-4)^m C_m`. This is equality of jets only, not
  convergence of the formal germ, equality on a neighborhood, or analyticity
  at the quarter anchor.

- `QuarterCatalanRichardson.lean` has three definitions,
  `finiteRescaleFilter`, `geometricRichardsonPowerSeriesFilter`, and
  `quarterCatalanRichardsonFilter`, and 15 theorems:
  `finiteRescaleFilter_coeff`,
  `geometricRichardsonPowerSeriesFilter_coeff`,
  `geometricRichardsonPowerSeriesFilter_coeff_zero`,
  `geometricRichardsonPowerSeriesFilter_coeff_eq_zero`,
  `geometricRichardsonPowerSeriesFilter_coeff_eq_qPochhammer`,
  `geometricRichardsonPowerSeriesFilter_coeff_eq_qBinomial`,
  `geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff_of_nonzero`,
  `geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff`,
  `quarterCatalanRichardsonFilter_coeff`,
  `quarterCatalanRichardsonFilter_coeff_zero`,
  `quarterCatalanRichardsonFilter_coeff_eq_zero`,
  `quarterCatalanRichardsonFilter_coeff_eq_zero_of_le`,
  `quarterCatalanRichardsonFilter_coeff_eq_qBinomial`,
  `quarterCatalanRichardsonFilter_coeff_succ_eq_qBinomial`, and
  `quarterCatalanRichardsonFilter_firstUncancelled_coeff`. These are strictly
  coefficientwise formal-power-series results: they preserve degree zero,
  cancel the prescribed low degrees, and identify all residual coefficients
  and the first survivor, without a convergence, real error-sign, remainder,
  or analytic-acceleration claim.

Finally, `sum_lagrangeEvalWeight_mul_pow_card_add_zero` in
`LagrangeResidualMoments.lean` gives every higher evaluation-at-zero moment
for a nonempty distinct field-valued node family as the negative signed nodal
product times the complete homogeneous function. The nonempty premise is
exactly what excludes the exceptional empty-row `0^0` term.

The normalized geometric-Lagrange and analytic Lagrange layers additionally
assume injectivity of `j |-> q^j` on the finite node set (see the status boxes and
crosswalk paragraphs inside the documents). `AnalyticSeriesFilter.lean` carries the core to exact
diagonal and Gaussian-tail identities for unconditionally summable sampled
series. Its hypotheses are sharp at zero-weight nodes. The current
`AnalyticMoments.lean` and `RvachevQBinomialFilter.lean` close the actual
infinite Rvachev-product specialization: for complex `c,z`, natural order `p`,
and Gaussian base `q = c^2`, only injectivity of `j |-> q^j` on
`range (p+1)` is assumed; `c = 1/2`, `q = 1/4` is assumption-free.
This does not formalize the reports' finite prefixes `P_(b,n)`, their
quotient or Bell coefficients, conditionally convergent boundary series, or
the analytic signs, error bounds, uniform/derivative convergence, and
asymptotics. `FiniteQBinomialCore.lean` zero-extends Gaussian lower indices
to all integers and proves total row reflection. `QBinomialVandermonde.lean`
separately proves both q-Vandermonde orientations, both central supports, the
three natural shifted forms, and the canonical forward backbone's single
shifted-central identity for every integer shift, all over arbitrary
commutative semirings.
`QPochhammerElementaryIdentities.lean` adds exactly 13 public theorems:
`finiteQPochhammerIn_base_reversal_units`,
`finiteQPochhammerIn_inv_base_reversal_units`,
`finiteQPochhammerIn_base_reversal`,
`finiteQPochhammerIn_inv_base_reversal`,
`prod_pow_sub_pow_eq_finiteQPochhammerIn`,
`pow_mul_finiteQPochhammerIn_inv_pow_eq`,
`finiteQPochhammerIn_inv_pow_eq_self_div`,
`finiteQPochhammerIn_inv_pow_eq_zero_of_lt`,
`one_sub_mul_gaussianBinomial_one`,
`gaussianBinomial_adjacent_mul`,
`gaussianBinomial_row_adjacent_mul`,
`gaussianBinomial_adjacent_div`, and
`gaussianBinomial_row_adjacent_div`. The two unit reversals, the root-safe
terminating numerator, the first-column clearer, and the two adjacent cross
identities hold over commutative rings. The two cross identities are total in
all `n,k`, including on and above the row boundary by zero extension. The
field reversal wrappers assume
exactly `a != 0` and `q != 0`; the cleared terminating formula and its
above-range zero theorem assume `q != 0`, while the displayed terminating
quotient also assumes `(q;q)_(N-k) != 0`. The adjacent quotient corollaries
remain restricted to `k < n` and instead assume exactly their displayed Gaussian and linear-factor
denominators are nonzero and do not require `q != 0`.

`QBinomialReciprocity.lean` adds exactly four public theorems:
`gaussianBinomial_reciprocity_units`, `gaussianBinomial_reciprocity`,
`gaussianBinomial_neg_one_eq_zero_of_odd_degree`, and
`gaussianBinomial_neg_one_even_odd_eq_zero`.  Unit reciprocity is total over
every commutative semiring; its semifield wrapper assumes only `q != 0`.
The two `q = -1` theorems hold over every commutative ring, including
characteristic two and above-diagonal zero-extension cases.  This proves the
reciprocity clause of the canonical forward backbone's compound structure
theorem, while its separate degree and coefficient-polynomial clauses keep
that full row partial.

`GaussianBinomialAtNegOne.lean` adds exactly five public theorems:
`gaussianBinomial_neg_one_even_even`,
`gaussianBinomial_neg_one_odd_even`,
`gaussianBinomial_neg_one_odd_odd`,
`finiteQPochhammerIn_neg_one_even`, and
`finiteQPochhammerIn_neg_one_odd`.  Together with
`gaussianBinomial_neg_one_even_odd_eq_zero` from the reciprocity module, these
give all four Gaussian parity values and both paired finite-product identities
over arbitrary commutative rings, without division or characteristic
restrictions.  `GaussianBinomialAtNegOneDerivative.lean` closes the companion
first-jet layer with exactly four public theorems: the even-degree derivative
law and total even-row/odd-column slope over every commutative ring, plus
root-multiplicity one first over `ℤ` and then over every characteristic-zero
commutative ring when `b<a`.  It does not assert simplicity in arbitrary
characteristic or at every cyclotomic zero.

The documents also cross-reference the independent real fractional-Volterra
layer. `FractionalVolterraCalculus.lean` proves positive affine covariance on
ordered intervals for arbitrary real order. For `alpha <= 0`, this covariance is
an identity for the totalized Lean interval-integral definition; a classical
Riemann--Liouville/integrability interpretation is asserted only for positive
order. Gamma-normalized order raising holds for real `alpha > 0` from a continuous Banach-valued primitive with an
interval-integrable right derivative. `FabiusFractionalVolterra.lean`
defines the total causal Rvachev fractional primitive, proves its support cutoff,
positive-natural bridge, and positive-order semigroup on `x >= -1`, and
specializes order raising to the signed Fabius extension for `x >= 0`, the
bounded Fabius function for `0 <= x <= 1`, and the Up-to-Fabius bridge for
`x >= -1`.
Complex orders, Caputo/Riemann--Liouville derivatives, weighted-monomial or iterated
shifts, negative-branch, shifted-lattice, endpoint-moment, transform/tail,
piecewise/refinement, and inverse/quantile formulas
remain research frontiers. These fractional-Volterra API claims were checked at source checkpoint
`149332f9d`.

Geometric-sinc subgroup member:
[`Exponents_and_q_Series_Frontiers/`](geometric-sinc-and-exponent-families/Exponents_and_q_Series_Frontiers/)
(retained historical PDF: 238 A4 pages and 6,953,898 bytes, SHA-256
`fa719a8ea68d3c474928b9fae7449f827eb35a5452613f2b660d8e88ba27267e`,
across seven parts). That PDF was rendered in three serial passes from the
preceding 16,274-line, 731,692-byte source checkpoint, SHA-256
`4be184dc95f7c9d7665e5edf56cd22dc66bdacbc2f113b03b700468836018f8b`;
the passes produced 228, 238, and 238 pages. Basic A4, text-extraction,
embedded-font, and no-Type-3 checks passed, but the containing batch stopped
before a fresh full log, page-box, and visual audit.

Earlier publication provenance includes a 238-page, 6,317,278-byte PDF with
SHA-256
`113d0318216db3ceaab160d0d1024f7adb48193420c385e700a7dd34c698b7cd`,
rendered from the 16,279-line source checkpoint
`d8b23a27965e0d242708e441d69d9a41fa5c7ac41f8146f12645d08ef6765dfe`.
Its final log had no fatal error, undefined reference, rerun request, or
missing-character diagnostic; all 238 pages were text-bearing, A4, rotation
zero, and raster-renderable, and its font and visual gates passed.

A parallel pre-replay receipt records a 238-page, 6,316,535-byte PDF with
SHA-256
`df7b9ad69e0310b17988dd42cc22559cf22ff26027395c005c374ad51f9e62aa`,
built in exactly three guarded passes from layout-fixed source
`2adbe7b1e450a858bb02e80e6b4c4c6420060733f2ae1fe25eb61b6546f58e0f`;
the pass page counts were 228, 238, and 238, its 41-input closure did not drift,
all 1,190 page boxes matched A4, and the recorded targeted visual inspection
was clean.  The later 16,344-line semantic-source checkpoint has SHA-256
`2c34d526f18379822ced4d807fd4049ecb85231f4a42a1cd2773fd3c990dd3b9`.

The retired-analysis-alias migration produced a 16,369-line, 737,768-byte
source checkpoint with SHA-256
`4313bddb87a0f248a8bad4bd5e5a7cfbb25da51d1b994abc0c9d4c62525ca78c`.
The live TeX changed again after that checkpoint and every named source/PDF
pair. Its final fingerprint is deferred until rebuild and ledger regeneration.
It adds the upstream
q-API material, exact zero-order/exponent identifiability with constructive
dyadic first differences, and the later normal-convergence and `6c7a69be9`
crosswalks, followed by the final eight-module q-calculus/theta tranche. The
exact `GeneralizedRvachevIdentifiability.lean` crosswalk gives constructive
dyadic-order first differences and full-product rigidity;
zeta-quotient, cumulant/analytic-sample, and probability-law identifiability
remain Partial in Lean. The retained PDF is therefore historical. The two
package ledgers explicitly omit the live TeX and certify the current historical
PDF plus unchanged stable payloads; final-source rendering, fingerprinting,
ledger regeneration, and full publication validation remain pending. This is the
2026-08-28 consolidation of the two former drafts (Part I:
Newton-basis frontiers; Part II: q-binomial Richardson), joined the
same day by the eighth-wave report as **Part III** — *Finite Dyadic
Sinc Products and Piecewise-Polynomial Approximants to Rvachev's
Up-Function* (formerly `finite_sinc_products_report/`): the exact
truncated-power formula for the prefix densities `p_n` with signed
Thue–Morse top-derivative jumps on a uniform dyadic knot grid, sharp
derivative plateaux, the exact error law
`||p_n^(r) − up^(r)||_∞ = 2^(C(r+3,2)−1)/(9·4^n)` with exact
Kolmogorov distance `1/(9·4^n)`, the Bell–Bernoulli all-orders
expansion, stable `q = 1/4` Richardson weights in closed q-binomial
form (extending Part II), a uniform scale-mixture representation
`X = R·U` of the up law, and a positive Gauss/Radau/Lobatto tail
quadrature hierarchy with exact constants — including the
variance-matched positive `16^{-n}` scheme that the frontier corpus
had proposed without construction, and a sixth-order exact-support
Radau rule — and by the two ninth-wave same-topic reports, **merged
editorially** (shared core stated once, constants cross-checked,
unique layers of each kept) as **Part IV** — *Fourier Images of the
Repeated-Integration Approximants* (formerly
`Rvachev_Piecewise_Approximation_Fourier_Images/` and
`rvachev_fourier_frontier_report/`): the master factorization
`f̂_n = Φ · A(2^{-n} t)` with the universal tail-transfer function
`A = sinc z / Φ(z)`, its cotangent and valuation-weighted canonical
products with signed divisor `1 − v₂(m)`, digit-sum zero counts and
the Thue–Morse sign law, exact Taylor radius `4π` with dominant-pole
coefficient asymptotics and an arithmetic Darboux hierarchy, the
complete finite/limit zero-multiplicity filtration, the sharp
`o(2^n)` relative-convergence window with forward/inverse
conditioning thresholds at `4π·2^n` and `π·2^n`, the impossibility of
globally stable convolutional deconvolution, weighted-`L^p` and
Sobolev all-orders norm laws with explicit leading constants, exact
algebraic mean-square Fourier tails with the sharp threshold
`f_n ∈ H^s ⟺ s < n + 1/2`, and positive moment-matched atomic,
dyadic-atomic, and polynomial-density closure menus at rates
`16^{-n}`–`256^{-n}`, compared as a family against Part III's box
mixtures.  A fifth part arrived with the tenth wave (formerly
`fabius_finite_products_frontier/`) — **Part V**, *Finite Dyadic Sinc
Products and Exact Transport Geometry of Rvachev Spline Approximants*:
convex-order and peakedness chains for the prefix laws, the exact
absolute moment `E|X_N| = 5/18 - 4^{-N}/9`, the fixed single crossing
of the density error at `x = +-1/2` for every stage, the exact metric
collapse `W_1 = d_K = 4^{-N}/9`, `TV = 2*4^{-N}/9`, stop-loss =
second-order Zolotarev = `4^{-N}/18`, `W_inf = 2^{-N}` with the
synchronous coupling optimal only at `p = inf`, the exact Thue-Morse
call-potential spline, the positive-mixture no-go theorem (no convex
combination of stages can cancel the leading error in any of these
metrics — signed Richardson weights are structurally necessary),
entropy/Fisher monotonicity with the exact criterion
`I(u_N) < inf iff N >= 3` and `KL(u || u_N) = inf`, and carefully
flagged conjectural weighted expansions (entropy, forward KL, Fisher,
fixed-p Wasserstein, and the `p ~ 2N` transport crossover with its
lower-Lambert phase).  The thirteenth wave added **Part VI** —
*Atomic Sinc-Product Splines Beyond the Binary Point* (formerly
`atomic_sinc_splines_report_package/`): an English translation and
frontier expansion of Rvachev's Chapter 3, treating the geometric
family `h_a` as a genuine deformation of `up = h_2` — the general
atomic-equation zero-matching criterion, closed Bernoulli cumulants
`κ_2m = 2^2m B_2m/(2m(a^2m − 1))` with Bell/Lambert moment calculus,
weighted Prouhet identities, exact derivative norms for `a ≥ 2`, the
fractal polynomial-gap atlas for `a > 2` with the complete
Taylor-germ trichotomy, the rational-power Strang–Fix reproduction
theorem, the all-orders prefix expansion with leading profile
`−h_a''/(6(a²−1))` (specializing at `a = 2` to the binary
constants of Parts III–V), the critical `a ↓ 2` collapse, the
reconstructed uniqueness theorem, and a conjecture register
(periodic-Lambert endpoint expansion, critical double scaling,
lattice obstruction without rational powers, strict log-concavity for
`1 < a < 2`).  The fourteenth wave brought a twin — *Atomic Functions
Beyond the Critical Dyadic Case* (formerly
`Atomic_Functions_Beyond_Dyadic_Report/`), a second independent
reconstruction of the same chapter — which was **merged editorially
into Part VI** (2026-08-28): the shared translation and `h_a` core are
stated once (both editions agreed on every commonly transcribed
equation), and its distinctive layers became dedicated sections — the
fractal-string geometry of `K_a` (geometric zeta
`ℓ₀^s/(1 − 2a^{−s})`, complex dimensions `D_a + 2πik/log a`, an exact
tube formula with continuous nonconstant one-periodic profile, hence
Minkowski non-measurability, with explicit logarithmic average), the
geometric local-degree law `P(N_a = r) = ((a−2)/a)(2/a)^r` with
`(a−2)/2 · N_a → Exp(1)` as `a ↓ 2` (the first marginal of the
critical double-scaling program), quantitative Gaussian (`a ↓ 1`) and
uniform (`a → ∞`) parameter limits with exact rates and an exactly
uniform expanding core, the exact general-base negative-Laplace
decomposition with real-analytic one-periodic correction whose
Fourier modes are `−Γ(−χ_k)ζ(1−χ_k)/log a` (settling the
transform-level half of the periodic-Lambert conjecture and pinning
the Lambert normalization `c_a = √a·log a/2`), the divisor-polynomial
form of `log M_a`, the canonical Fup ladder `G_n → 2·up(2x)`, and
three new register entries (overlap-regime nowhere analyticity,
algebraic-breakpoint arithmetic, a bridge between the two periodic
profiles).  The fifteenth wave brought a third reconstruction of the
same chapter — *Atomic Functions, Rvachev's up-Function, and Smooth
Cantor Splines* (formerly `Rvachev_Atomic_Functions_Report/`) — which
was likewise **merged editorially into Part VI** (2026-08-28),
contributing the signed leading coefficient
`L_ω = (−1)^{N₊(ω)} a^{(r+1)(r+2)/2}/(2^{r+1} r!)` on every gap, the
derivative equimeasurability theorem with the full `L^p` ladder
`‖h_a^{(n)}‖_p = (a^{n(n+3)/2}/2^n)(2/a)^{n/p} ‖h_a‖_p` and the exact
derivative-value mixture law, the endpoint jet-reduction form of the
one-branch formula (the exact
Bernoulli→cumulants→moments→jets→gap-polynomials engine), the
classical `Fup_n` hierarchy with its exact triangular reconstruction
of `up` by `n(n+1)/2` dyadic averaging steps, closed cumulants
(`σ_n² = 4^{−n}(3n+4)/36`), and quantitative central-limit regime
(Berry–Esseen `O(n^{−1/2})`), the edge pantograph equations
generalizing `F′ = 2F(2·)` to every base, and further register
entries (`Fup_n` Edgeworth, graph-directed atomic splines,
pressure-function Taylor multifractal).  The sixteenth and seventeenth
waves arrived as same-topic twins on the signed and reciprocal
parameter orbit `{q, −q, 1/q, −1/q}` of the geometric-uniform family
and were **merged editorially as Part VII** — *Signed and Reciprocal
q-Fabius Frontiers* (formerly `Fabius_Q_Connections_Report/`, *Beyond
the Dyadic Fabius Web*, and `Signed_Reciprocal_q_Fabius_Frontiers/`):
affine sign conjugacy (negative q creates no new normalized shapes),
the reciprocal moment germ with `M_q(t)·M_{1/q}(−t) = 1` and finite
digit-reversal duality giving `q = ±2, ±4` exact meaning, geometric
multisection (whose fixed normalized half--quarter series, product-law,
and scaled-measure convolution are now formal, while the general `q,m`, MGF,
cumulant, centered-density, and spectral forms remain frontier), the spectral
q²-Pochhammer factorization, the
Bernoulli cumulant dictionary with closed spectral zeta, log-concavity
with the exact plateau phase `|q| ≤ 1/2`, the positive Laplace
representation of reciprocal germs (vertical-line moments, Hankel
signature `(−1)^C(n,2)`, orthogonal polynomials on `Re z = 1/2`), the
q-Fabius–Bernoulli Appell deconvolution family, the moment polynomial
`𝒫_n(q)` with its odd-q-integer divisor conjecture, the two-nome
Pochhammer–Prouhet partition function and digit-position master
product, the exact q-Prouhet moment transfer, the
Grassmannian/Hermitian finite-geometry square, box-spline derivative
combs with the dimension-1/2 quartic Cantor skeleton, reciprocal
q-Lagrange row reversal, the exact inverse-geometric endpoint lattice
`G_q(qⁿ) = q^C(n+1,2)·𝒫_n/(q;q)_n` with all jets and new
inverse-quartic values, the uniform two-term endpoint asymptotic with
its square-root/log-log inversion, and the resolution of the
sixteenth wave's periodic-cocycle conjecture by Part VI's exact
Gamma–zeta Laplace decomposition.  The eighth-wave fold also
repaired the volume's part-boundary section numbering (Part II had
rendered with `\appendix` letters G–N).  Supporting files under
`assets/`, provenance with SHA-256 in the document itself.  For the spectral
q²-Pochhammer theorem, the current Lean crosswalk proves the general inside
product but remains partial at the surrounding wrappers.  The sinc-product
API proves, for real `|q| < 1`, the uncentered real-frequency identity
`φ_q(t) = exp(i t/2)·S_q((1-q)t/(2π))` and, for complex `‖q‖ < 1`, locally
uniform convergence and entire-ness of `S_q(z) = ∏ sinc(πqⁿz)`.  The
Pochhammer module now proves absolute summability of the paired Euler
perturbations and the global rearrangement
`S_q(z) = ∏_k (z²/(k+1)²;q²)_∞` for every strict complex contraction,
including `q = 0` and individual zero factors.  What remains outside Lean is
the named centered/MGF packaging, the reciprocal outside-disk formula,
zero–pole exchange, and a packaged compact-uniform theorem for the full
phase-bearing characteristic prefixes.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.

The two revised fourteenth-wave editions
(`Atomic_Functions_Beyond_Dyadic_Report-2/`, `-3/`) were merged into Part VI
(2026-08-28): the Orlicz/rearrangement form of derivative equimeasurability,
the spectral Stieltjes–Wigert bridge (squared-frequency moments
`a^{n(n+2)}/2^n`, an explicit non-lognormal representing measure with closed
Hankel determinants and orthogonal polynomials), the Mellin law of the
distance to `K_a` (complex dimensions shifted by −1; distribution function =
the exact tube formula), and — for provenance — the eleven-page Russian
source scan itself, against which the translation layers were checked (the
scan and the raw OCR were both deleted once their recoverable content was
merged and verified; SHA-256 hashes stay in the volume's provenance list,
the repair ledger lives in Part VI's concordance appendix, and git history
archives the files).  The revised fifteenth-wave
edition (`Atomic_Functions_Rvachev_Report_Package/`) followed: the
q-Gaussian derivative Gram kernel `q^{(j−k)²}` with Pochhammer determinants
and sharp Jacobi-theta Riesz bounds, the log-Weibull jet-intermittency law,
and the proof of the uniform all-orders `Fup_n` Edgeworth expansion
(resolving that register conjecture).  An expanded fifteenth-wave edition
(`Atomic_Functions_Rvachev_Expanded_Report/`, audit-aware — it marks the
previously merged layers as inherited baseline) closed the Gram geometry:
the Gaussian-binomial Gram–Schmidt theorem
`ψ*_n = Σ_j q^{n−j}·[n,j]_{q²}·e_j` with norms `(q²;q²)_n`, explicit
Cholesky and inverse Gram, the Rogers–Szegő identification of the
orthogonalizers, the uniform-innovation corollary (each new derivative
keeps an innovation of norm at least `(q²;q²)_∞^{1/2}`), the
wrapped-heat-kernel circle model (each parity tower is unitarily the
monomial sequence against `ϑ₄(θ/2, 1/a)` — heat time `log a`), the
MacMahon determinant constant `𝔐(a⁻²)` with parity-factored full-sequence
determinants and triple-product Riesz forms with a verified numeric table,
and the overlap-regime theta conjecture for `1 < a < 2`; its figures and
data live under `assets/Atomic_Functions_Rvachev_Expanded_Report/`.  Two
expanded fourteenth-wave editions
(`Atomic_Functions_Beyond_Dyadic_Expanded/`,
`Atomic_Functions_Beyond_Dyadic_Frontiers/`; both audit-aware, both
re-shipping byte-identical copies of the source scan/OCR, again not
retained) closed the round with disjoint layers: the physical-space
Stieltjes–Wigert differential ladder `Υ_{a,n} = P_{a,n}(−d²/dx²) h_a`
(compactly supported orthogonal system, closed norms, q-binomial
derivative expansion, three-term operator recurrence) — identified during
the merge with the fifteenth wave's Gram–Schmidt vectors,
`Υ_{a,n} = (−1)^n ‖h^{(2n)}‖₂ ψ*_n`, a check that also caught and repaired
a sign-convention slip in the closed Gram–Schmidt theorem's first
printing — plus both parity derivative-jet Gram determinants, the
autocorrelation germ `a^{n(n+2)}/2^n` with zero Taylor radius and provable
ladder incompleteness, and the explicit-null-modes conjecture; and the
exact derivative-energy factorization
`μ_{a,n,p} = Law(S_{a,n} + a^{−n} Y_{a,p})` with `W∞ ≤ 2a^{−n}/(a−1)`
convergence to the symmetric Bernoulli convolution (Cantor measure on
`K_a` for `a > 2`, uniform at `a = 2`), exact Hausdorff support rate, the
Rényi/Shannon entropy laws `H_β(n) = H_β(0) + n log(2/a)` with the
information-dimension reading, and the overlap-regime energy conjecture;
their figures and data live under the matching `assets/` directories.
Two expanded fifteenth-wave editions
(`Atomic_Functions_Rvachev_Report_Expanded/`,
`Atomic_Functions_Rvachev_qBinomial_Frontiers/`; both audit-aware; the
first also re-shipped the two previous editions of its lineage alongside
the scan/OCR — all byte-identical to recorded files, none retained)
completed the orthogonalization and jet theory: the nodal-polynomial
reading of the Gram–Schmidt residuals (interpolation at geometric nodes;
pivot = value at the next node), the exact inverse transform with the
entrywise-positive Cholesky factorization, the minimum-phase theta
whitening filter `A_q(z) = 1/(−qz;q²)_∞` with
`|A_q|²·ϑ₃ = (q²;q²)_∞` (the Szegő factor of the q-Gaussian covariance),
Schur-minor strict total positivity of the kernel with
oscillation/checkerboard consequences, the two-term jet tail with the
sharp exponential-Orlicz threshold, and the highest-jet partial-theta law
with the joint jet–distance transform (the distance-Mellin pole lattice
deforms into an entire partial theta series for `s > 0`); five register
conjectures were added and the algebraic-breakpoint conjecture gained its
transcendental-dichotomy sharpening; figures and data live under the
matching `assets/` directories.
(The q-orbit reports `Fabius_Q_Connections_Report/` and
`Signed_Reciprocal_q_Fabius_Frontiers/` were merged editorially as the
volume's Part VII; their figures/data are likewise under `assets/`.)

Canonical forward/inverse publication:
[`q_pochhammer_q_binomial_monograph/`](q_pochhammer_q_binomial_monograph/)
(current TeX with a retained historical A4 publication checkpoint; exact
receipt in the detailed package record above) — *q-Series and Inverse q-Analogs:
A Proof-Oriented Synthesis*. Its forward backbone proves from first principles
the shifted-factorial, Gaussian, hypergeometric, theta, partition, Bailey,
cyclotomic, interpolation, and Fabius--Rvachev machinery consumed by Parts II,
VI, and VII of the frontier volume and by the repository's formalized
Gaussian-binomial core. It retains the former monograph's formula atlas, limit
dictionary, proof-dependency guide, and formalization architecture, and now
places that material in the same master as the branch-aware inverse theory.
The forward backbone was audited on arrival: ten core theorems were
re-verified symbolically; the Chern--Dilcher--Jiu deleted-singularity identity
and Ramanujan's ₁ψ₁ were verified numerically to 30 digits; and one
dominated-convergence majorant was repaired with an `% ed.:` note. Its last
pre-consolidation rendered checkpoint had 13,117 source lines (SHA-256
`29d7b1d4bd2e5601f4eee63acc1ff7ef3f5f904e0f5f3b8474ce6c51a2129cca`)
and a 1,582,997-byte, 213-page PDF (SHA-256
`7ee6f8f6d8e72228a5b20daa119caa4d834b11063f910b526897b2677a2ede7b`).
Those figures identify a retired historical artifact; they are not build
claims about the current canonical source. The canonical synthesis's current
source and retained historical PDF are identified by the single exact receipt
in the detailed package record above.

The latest validated forward formalization ledger has 282 rows: 80 Exact, 86
Partial, 108 with no counterpart, and 8 N/A interface rows. The original
191-result pre-Fabius core had 36 exact, 29 partial, 123 with no counterpart,
and 3 interface-only entries. The four integrated-guide chapters add 31
human-proved but not Lean-formalized assertions and five labelled definitions;
the later Fabius bridge contributes the remaining rows. Its pointwise
inside-`q^2` Pochhammer factorization and the outer product's locally uniform
(normal) convergence are now formal for every complex strict contraction,
including `q = 0`. The compound spectral theorem remains partial at its named
centered/MGF wrappers and exterior reciprocal clauses. The algebra of
q-shifted factorials now accounts for 11 exact, 2 partial, and 2
unformalized results; the q-integer and Gaussian-coefficient chapter for
8 exact, 1 partial, and 0 unformalized results. The finite
q-binomial/inversion chapter now accounts for 9 exact, 1 partial, and 0
unformalized results; the weighted chapter for 3 exact, 2 partial, and 3
unformalized results; and the basic-hypergeometric chapter for 1 exact, 3
partial, and 5 unformalized results. The cyclotomic chapter now has 6 exact,
1 partial, and 2 unformalized results; q-gamma/q-beta has 3 exact, 1 partial,
and 4 unformalized results; and negative upper indices/geometric Newton has 2
exact, 2 partial, and 5 unformalized results. The exact rows include the primary and
second q-Cauchy identities, both weighted-Pascal recurrences,
elementary--complete orthogonality, and weighted symmetric-function inversion.
Their adjacent strengthenings are recorded human-readably in the canonical
forward backbone:
reflected q-Cauchy and the q-Bernstein partition of unity, plus total
empty-family and degree-zero boundaries. Weighted generating products and the
reciprocal finite theorem are partial because their formal power-series
identities are exact while their analytic evaluation and convergence clauses
remain open. The q-Pfaff--Saalschütz summation remains unformalized; no status
is inferred from a related finite identity. These counts and boundaries were
statically cross-checked against the exhaustive public surfaces of
`QBinomialCauchy.lean` (one definition and five theorems, including the
compatibility spelling of its primary identity),
`SymmetricFunctionOrthogonality.lean` (one definition and six theorems),
`FiniteTriangularTransform.lean` (one definition and one theorem),
`SymmetricFunctionTransform.lean` (four definitions and five theorems), and
`SymmetricFunctionGenerating.lean` (two definitions and six theorems),
`QDifferenceAnnihilation.lean` (four theorems),
`QBinomialInversionSpecializations.lean` (two definitions, four theorems),
`QPochhammerElementaryIdentities.lean` (13 theorems),
`QPochhammerDissection.lean` (two theorems),
`QPochhammerInfinite.lean` (one definition, 29 theorems),
`QBinomialReciprocity.lean` (four theorems),
`GaussianBinomialPalindromic.lean` (zero definitions, twelve theorems),
`GaussianBinomialPolynomialStructure.lean` (zero definitions, five theorems),
`CentralQBinomialReduction.lean` (zero definitions, six theorems),
`CyclotomicFactorization.lean` (zero definitions, seven theorems),
`PrimitiveRootBlock.lean` (zero definitions, three theorems),
`QLucas.lean` (zero definitions, eight theorems),
`CyclotomicDivisibility.lean` (zero definitions, three theorems),
`QCatalan.lean` (one definition, eleven theorems),
`NewtonInterpolation.lean` (two definitions, thirteen theorems),
`QBetaIntegral.lean` (one definition, eight theorems),
`GaussianBinomialAtNegOne.lean` (five theorems),
`RvachevPochhammerFactorization.lean` (one definition, ten theorems),
`QPochhammerEntire.lean` (zero definitions, five theorems),
`GeometricPochhammerNormalConvergence.lean` (zero definitions, three theorems),
`GaussianBinomialContinuity.lean` (zero definitions, three theorems),
`JacobiTripleProduct.lean` (two definitions, twenty-five theorems),
`QBinomialTheoremInfinite.lean` (one definition, twenty-two theorems),
`QPascalSummation.lean` (zero definitions, four theorems),
`QuantumBinomial.lean` (zero definitions, two theorems), and
`RogersSzegoPolynomial.lean` (one definition, nine theorems), together with
the earlier source-union modules `JacksonIntegral.lean` (1+7), `QExponential.lean` (3+8),
`ThetaQuasiPeriodicity.lean` (1+6), `JacobiCubic.lean` (0+2),
`QPochhammerLogDerivative.lean` (0+10),
and `QPochhammerOrderDerivative.lean` (0+3).
The five `GaussianBinomialAtNegOne` theorems are
`gaussianBinomial_neg_one_even_even`,
`gaussianBinomial_neg_one_odd_even`,
`gaussianBinomial_neg_one_odd_odd`,
`finiteQPochhammerIn_neg_one_even`, and
`finiteQPochhammerIn_neg_one_odd`. The first three together with the reused
`gaussianBinomial_neg_one_even_odd_eq_zero` theorem from
`QBinomialReciprocity` prove the forward backbone's complete `q = -1` value
formula over every commutative ring, for all natural parameters including
above-row zero extension. Lean now proves the evaluated-root q-Lucas identity
in `gaussianBinomial_q_lucas`, but not the printed polynomial congruence modulo
`Φ_d`; that row is therefore Partial pending the minimal-polynomial lift.
The q-difference annihilation row is exact through
`qDifference_sum_eval₂_eq_zero_of_degree_lt`, with the stronger
characteristic-polynomial, all-moment, and scalar-extension top-coefficient
results recorded alongside it. The chapter's alternating sums, both
weighted-subset conventions,
named module-valued inversion iff, and both kernel orthogonalities are exact.
Both orientations
of q-Vandermonde and both central-support presentations are exact in
`QBinomialVandermonde.lean`; the canonical forward backbone's single signed
shifted-central formula is now exact for every integer shift through the zero-extended
`gaussianBinomialInt`, both as a finite natural-range sum and literally as a
finite-support `finsum` over all integers. The ledger also now records the
genuine real infinite product `qPochhammerInf` and its contractive-base
convergence/positivity layer, replacing the stale claim that every infinite
q-Pochhammer in the development was merely a finite `Finset.range` product.
For every fixed complex strict contraction, the separate complex symbol now
has locally uniform convergence on the whole parameter plane, is entire in
that parameter, has exactly its displayed factor zeros (including at the
degenerate nome zero), and every zero has analytic order one. The geometric
sinc product has a global spectral factorization for every complex strict
contraction with nome `q^2`; only the two final Rvachev wrappers specialize to
nome `1/4`. The compound spectral theorem in the Fabius bridge remains
partial because its named centered/MGF wrapper, outside-disk reciprocal
formula, pole divisor, and zero--pole exchange are not formalized. Its outer
local-uniform/normal-convergence clause is exact.
The complementary formal surfaces of
`CompleteHomogeneousGenerating.lean` and
`SymmetricFunctionGenerating.lean` prove both the finite elementary product
and complete-homogeneous reciprocal product; the labelled weighted theorem
remains partial only because its analytic evaluation and convergence clause
is open. `CompleteHomogeneousAsymptotics.lean` adds the fixed-degree
coordinatewise-Big-O transfer, but does not close that analytic boundary.
Separately,
`SymmetricFunctionOrthogonality.lean` proves the displayed
elementary--complete coefficient convolution exactly over every commutative
ring, including the empty family and degree zero.

`QBinomialCauchy.lean` gives the exact primary convolution under the canonical
name `Fabius.finite_qCauchy_identity` and the compatibility spelling
`Fabius.finiteQPochhammerIn_mul_eq_sum_gaussianBinomial`, together with its
reflected orientation, the denominator-free q-Bernstein partition of unity,
and the exact finite Cauchy convolution II. All parameters and degrees are
arbitrary over every commutative ring, so no cancellation, nonvanishing,
injectivity, topology, or convergence hypothesis is needed. The later
q-Pfaff–Saalschütz summation and infinite-product consequences remain
unformalized.

The wave volumes' central probabilistic object — the normalized
geometric-uniform law `Y_q = (1-q)·∑ qʲU_j`, with `q = 1/2` the
Fabius case and `q = 1/a` the atomic family `h_a` — now carries the
kernel-verified four-face geometric-tail dictionary at every ratio
`|q| < 1`: `GeometricUniformDictionary.lean` converts the corpus's
product-form self-similarity into convolution form and instantiates
`geometric_tail_dictionary` — the measure, characteristic-product,
moment, and cumulant faces of the `m`-digit tail in one statement.
The separate fixed two-section layer in
`GeometricUniformMultisection.lean` has exactly two public definitions,
`Fabius.ProbabilityRepresentation.evenCoordinates` and
`Fabius.ProbabilityRepresentation.oddCoordinates`, and three public theorems:
`Fabius.ProbabilityRepresentation.geometricUniformSeries_one_half_multisection`,
`Fabius.ProbabilityRepresentation.geometricUniformDistribution_one_half_multisection`,
and
`Fabius.ProbabilityRepresentation.geometricUniformDistribution_one_half_conv_one_quarter`.
They prove, without user hypotheses, the pointwise normalized identity
`Y_(1/2)(ω) = (2/3)Y_(1/4)(ω_even) + (1/3)Y_(1/4)(ω_odd)`, the independence and
product-map law of the two parity processes, and the equivalent convolution of
the `2/3`- and `1/3`-scaled quarter laws.  This does not by itself prove a
general multisection theorem, the centered-density formula, or the MGF,
cumulant, Fourier, Pochhammer, `Z`, and comb identities in Part VII.
The characteristic-product face is now closed in elementary terms:
`GeometricSincFactorization.lean` computes the digit,
`φ_digit(t) = e^{i(1-q)t/2}·sinc((1-q)t/2)`
(`Fabius.charFun_geometricUniformDigit`), and proves the **finite sinc
factorization at every ratio**
`φ_q(t) = e^{i(1-q^m)t/2}·∏_{k<m} sinc((1-q)q^k t/2)·φ_q(q^m t)`
(`Fabius.charFun_geometricUniformDistribution_prefix_sinc`, with the
raw closed-factor form `_prefix`) — the finite half of Part IV's master
factorization `F̂ₙ = Φ·A(2⁻ⁿs)` at `q = 1/2` and of Part VI's `ĥ_a`
sinc products at `q = 1/a`, kernel-verified.

The final analytic bridge consists of exactly eight public theorems. For
complex `q,z` with `‖q‖ < 1`, writing
`S_q(z) = geometricSincProduct q z = ∏_{n≥0} sinc(πqⁿz)`, the four theorems
`Fabius.hasProdLocallyUniformly_geometricSincProduct`,
`Fabius.geometricSincProductFactors_multipliable`,
`Fabius.hasProd_geometricSincProduct`, and
`Fabius.geometricSincProduct_differentiable` give locally uniform product
convergence, genuine pointwise `Multipliable` and `HasProd` witnesses with
that exact value, and entire-ness. For real `|q| < 1`, `t ∈ ℝ`, and
`z_q(t) = (1-q)t/(2π)`, including `q = 0` and negative contractions,
`Fabius.charFun_geometricUniformDistribution_eq_phase_mul_geometricSincProduct`
and
`Fabius.charFun_geometricUniformDistribution_eq_phase_mul_geometricReciprocalGamma`
give
`φ_q(t) = exp(i t/2)·S_q(z_q(t)) = exp(i t/2)·G_q(z_q(t))·G_q(-z_q(t))`,
where `G_q(z) = geometricReciprocalGamma q z`. The further theorems
`Fabius.tendstoLocallyUniformly_prefix_sinc_charFun` and
`Fabius.tendstoUniformlyOn_prefix_sinc_charFun` prove that the full
phase-bearing finite prefixes converge locally uniformly on the real
frequency line, and uniformly on every compact real frequency set, to
`φ_q`. These statements still use only `|q| < 1`, so they include `q = 0`
and negative contractions.

`RvachevPochhammerFactorization.lean` adds the exhaustive complex
Pochhammer surface: the one definition `Fabius.complexQPochhammerInf` and
the ten theorems `Fabius.complexQPochhammerInf_eq_tprod`,
`Fabius.complexQPochhammerInf_eq_qPochhammerInfIn`,
`Fabius.multipliable_one_sub_mul_pow_complex`,
`Fabius.hasProd_complexQPochhammerInf`,
`Fabius.tendsto_finiteQPochhammerIn_complex`,
`Fabius.summable_norm_sineTerm_qpow_pair`,
`Fabius.geometricSincProduct_eq_tprod_pair`,
`Fabius.geometricSincProduct_eq_tprod_complexQPochhammerInf`,
`Fabius.rvachevFourierProduct_eq_tprod_complexQPochhammerInf`, and
`Fabius.rvachevFourier_eq_tprod_complexQPochhammerInf`. The new equality to
`Fabius.qPochhammerInfIn` is an unconditional definitional bridge and needs no
contraction hypothesis. The symbol is total; the named multipliability,
product, and finite-prefix convergence theorems require exactly `‖q‖ < 1` and
allow arbitrary complex `a`. The two dyadic
spectral theorems are the last two: they fix the scale and nome `1/4`, hold for
every complex `z` including at zero factors, and the Fourier form assumes
exactly a bounded Fabius witness satisfying `IsFabius`.  Before those
specializations, `geometricSincProduct_eq_tprod_complexQPochhammerInf` proves
globally for every complex `q,z` with `‖q‖ < 1` that
`S_q(z) = ∏'_k (z^2/(k+1)^2;q^2)_∞`; the paired-index and absolute-summability
theorems justify the exchange of scale and spectral-zero indices, including
`q = 0`, negative and nonreal contractions, and zero factors.

`QPochhammerDissection.lean` proves
`Fabius.finiteQPochhammerIn_dissection` and
`Fabius.finiteQPochhammerIn_dissection_remainder` over every commutative ring;
the latter allows the stronger boundary `u <= r`. `QPochhammerInfinite.lean`
adds the generic definition `Fabius.qPochhammerInfIn` and 29 theorems. For a
fixed contracting nome they include finite-prefix convergence, natural-number
finite shifts, factor removal, infinite dissection, and the exact zero locus;
over the complex numbers they include local uniformity in `a`, entire-ness,
and an explicit nonzero derivative at every zero `q^(-j)`. The new
`Fabius.deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one` is the division-free
derivative-nonvanishing statement at every raw factor zero `a*q^j = 1`, so it
also covers `q = 0`; `Fabius.analyticOrderAt_qPochhammerInfIn_of_eq_zero`
then states that every zero has analytic order exactly one, again including
`q = 0`. Thus the finite
dissection and remainder rows are exact, while the arbitrary-complex-order
concatenation row is only partial. Infinite dissection assumes a positive
modulus, while the two finite dissection theorems require no contraction or
nonvanishing. These free-parameter regularity results prove neither joint
`(a,q)` holomorphy nor continuation in the nome, and they do not supply the canonical chapter's
explicit uniform-in-`q` tails and derivative kernels.

`QPochhammerEntire.lean` retains the four earlier compatibility theorems and
adds the analytic-order compatibility theorem, for exactly five public theorems:
`Fabius.hasProdLocallyUniformly_complexQPochhammerInf`,
`Fabius.complexQPochhammerInf_differentiable`,
`Fabius.complexQPochhammerInf_eq_zero_iff`,
`Fabius.complexQPochhammerInf_eq_zero_iff_eq_inv_pow`, and
`Fabius.analyticOrderAt_complexQPochhammerInf_of_eq_zero`. For each fixed
complex `q` with `‖q‖ < 1`, these transfer the generic `qPochhammerInfIn`
results to the older `complexQPochhammerInf` names rather than duplicating
their analytic proofs. They expose local uniform convergence of the
defining factors on the whole complex `a`-plane, entire-ness in `a`, the raw
factor-zero locus `∃ j, 1 - a*q^j = 0`, and analytic order one at every zero.
The division-free zero statement includes `q = 0`; for `q ≠ 0`, the additional
compatibility theorem gives the reciprocal-power zero lattice. The module
asserts neither joint holomorphy in `q` nor local uniformity of the outer
spectral product; the latter is supplied separately by
`GeometricPochhammerNormalConvergence.lean` below.

The
eight-theorem sinc-product tranche above
supplies the general-`q` uncentered real-frequency bridge, locally uniform
entire `S_q`, and real-frequency local and compact uniform convergence of the
full phase-bearing prefixes.  There is still no named centered or MGF wrapper
or outside-disk reciprocal formula. Parameter-local statements in the generic
leaves alone do not imply joint nome analyticity.

`GeometricPochhammerNormalConvergence.lean` adds zero definitions and exactly
three public theorems. The general theorem
`Fabius.hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`
proves local-uniform convergence on the whole complex plane of the outer
nome-`q^2` Pochhammer product to `S_q` for every complex strict contraction,
including `q = 0`. The other two declarations specialize to the nome-`1/4`
Rvachev product and then to the Fourier transform of every bounded Fabius
witness satisfying `IsFabius`:
`Fabius.hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`
and `Fabius.hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf`.
This closes the outer normal-convergence
subclaim only; the named centered/MGF and exterior reciprocal/pole packaging
of the compound manuscript theorem remains Partial.

`QPochhammerDissection.lean` adds the two denominator-free finite residue-class
factorizations over arbitrary commutative rings. `QPochhammerInfinite.lean`
adds the generic infinite symbol `Fabius.qPochhammerInfIn` and 29 theorems:
strict-contraction summability and convergence, finite-prefix and residue-class
factorizations, exact zero criteria, locally uniform parameter convergence,
continuity and complex differentiability, nonzero derivatives at every raw
factor zero including `q = 0`, and analytic order one at every zero. Its
infinite dissection assumes a positive modulus, while the two finite dissection
theorems require no contraction or nonvanishing. These APIs are regularity
statements in the free parameter, not joint analyticity or continuation in the
nome.

`GeometricPochhammerNormalConvergence.lean` closes the former outer-product
boundary with exactly three public theorems.  They give locally uniform
convergence of the complex q-Pochhammer product over the spectral index to the
general geometric sinc product for every strict complex contraction, specialize
it to the dyadic standalone Rvachev Fourier product with nome `1/4`, and
transport it to the Fourier transform of every bounded Fabius witness.  The
general statement includes `q = 0`; it is not a joint-holomorphy theorem in the
nome.

`GeneralizedRvachevIdentifiability.lean` has zero definitions and six
theorems.  It identifies dyadic analytic orders with inclusive exponent
prefixes, decodes the head and successive exponents by first differences,
recovers the exponent sequence, and makes equality of admissible generalized
products equivalent to equality of exponents.  It does not identify from a
bare zero set, cumulant samples, or a probability law.

The six newly crosswalked modules contribute 69 public declarations.
`GaussianBinomialContinuity.lean` has zero definitions and three theorems:
continuity and the `q → 1` classical limit hold for every natural row and
column over a topological semiring, including the zero-extended boundary, while
its separate quotient theorem keeps `k ≤ n` and a nonzero finite denominator.
`QPascalSummation.lean` has zero definitions and four theorems, giving total
finite Pascal sums (including the noncommutative left-coefficient form) and
the two root-namespace `Commute.gaussianBinomial_left` and
`Commute.gaussianBinomial_right` wrappers. `QuantumBinomial.lean` has zero
definitions and two theorems; its ordered expansion is division-free over an
arbitrary semiring under the stated commutation relations and includes `n = 0`.

`JacobiTripleProduct.lean` has two definitions and twenty-five theorems. Its
finite polynomial identity is ring-level and total, its Laurent form requires
only `z ≠ 0`, and its Jacobi and pentagonal `HasSum` results require a complete
normed field with `‖q‖ < 1`, including `q = 0`; the bilateral results do not
extend to `z = 0`. `QBinomialTheoremInfinite.lean` has one definition and
twenty-two theorems: under `‖q‖ < 1`, Euler's product holds for every series
variable, while the infinite q-binomial and reciprocal expansions additionally
require its norm to be below one; `q = 0` is included. The ownership of
`Fabius.finiteQPochhammerIn_zero_left` remains with
`GaussianBinomialAtOne.lean`, so it is not counted again here.
`RogersSzegoPolynomial.lean` has one definition and nine theorems: its finite
identities are algebraic, while the generating-function `HasSum` theorem needs
exactly `‖q‖ < 1`, `‖t‖ < 1`, and `‖z * t‖ < 1`, with no separate bound on
`z` and with `q = 0` and `t = 0` included.

The five `6c7a69be9` q-series leaves contribute exactly 50 more public
declarations: `ClassicalPochhammerLimit.lean` has five theorems;
`GaussianBinomialUniversal.lean` has two; `PolynomialQTaylor.lean` has two
definitions and 18 theorems; `QPartialFractions.lean` has one definition and
five theorems; and `QPochhammerIntegerIndex.lean` has two definitions and 15
theorems.  They add the classical q-to-one Pochhammer limit, universal
Gaussian-polynomial evaluation, iterated q-derivatives and the q-Taylor
formula, finite q-partial fractions, and signed integer-index symbols with
concatenation laws.

The five newest analytic q-series leaves contribute 26 public declarations.
`BasicHypergeometricSeries.lean` has two definitions and five theorems: for
`‖q‖ < 1` and nonvanishing denominator products, absolute convergence holds
for every `z` when `r ≤ s`, and for `‖z‖ < 1` when `r = s + 1`.
`HeineTransformation.lean` has two definitions and five theorems, retaining
its strict nome and argument contractions and each displayed nonvanishing
hypothesis. `QGaussSummation.lean` has zero definitions and two theorems, on
the specialization domain stated by its strict norm, nonzero-parameter, and
nonvanishing-product hypotheses. `QPochhammerInfiniteBounds.lean` has zero
definitions and five theorems for the uniform product and reciprocal-prefix
bounds. `QPochhammerComplexOrder.lean` has one definition and four theorems;
its complex powers use the principal branch, and its concatenation and shift
identities retain their explicit nonvanishing conditions.

`QMultinomial.lean` has one definition and nine theorems, including the empty
and singleton boundary values. Its semiring-level recursion, pair reduction,
naturality, and universal-polynomial evaluation are division-free; the
factorial identity is ring-level, and the quotient form retains its stated
nonzero-denominator hypothesis over a field.

`CentralQBinomialReduction.lean` has zero definitions and exactly six
theorems: `finiteQPochhammerIn_mul_neg`,
`finiteQPochhammerIn_two_mul`, `finiteQPochhammerIn_map_ringHom`,
`central_gaussianBinomial_sq_mul_int`,
`central_gaussianBinomial_sq_mul`, and
`central_gaussianBinomial_sq_div`. The first five give sign pairing,
even--odd dissection, naturality, and the universal and general
division-free central reductions over polynomial or arbitrary commutative
rings. The quotient wrapper is over a field and assumes exactly that
`finiteQPochhammerIn (-q) q (2*k)` and
`finiteQPochhammerIn (q^2) (q^2) k` are nonzero.

`CyclotomicFactorization.lean` has zero definitions and exactly seven
theorems: `div_add_div_le_div`, `div_le_div_add_div_add_one`,
`mem_range_and_mem_divisors_iff`,
`finiteQPochhammerIn_X_eq_prod_cyclotomic`,
`finiteQPochhammerIn_X_eq_gaussianBinomial_mul`,
`prod_cyclotomic_pow_div_extend`, and
`gaussianBinomial_X_eq_prod_cyclotomic`. The first two inequalities show that
the Gaussian cyclotomic exponents are in `{0,1}`. The shifted-factorial
factorization and factorial identity hold over every commutative ring; only
the final cancellation to the Gaussian factorization requires an integral
domain, and the Gaussian statements retain `k ≤ n`.

`PrimitiveRootBlock.lean` has zero definitions and exactly three theorems:
`gaussianBinomial_isPrimitiveRoot_eq_zero`,
`neg_one_pow_mul_pow_choose_two`, and
`finiteQPochhammerIn_isPrimitiveRoot`. They work over a commutative integral
domain at a primitive `d`th root. Interior Gaussian vanishing assumes exactly
`0 < k < d`; the phase and complete root block explicitly assume `0 < d`.

`QLucas.lean` has zero definitions and exactly eight theorems:
`two_mul_choose_two`, `add_mul_add_sub_one`, `choose_two_add`,
`coeff_finiteQPochhammerIn_neg_X`, `finiteQPochhammerIn_neg_X_block`,
`coeff_block_pow_mul`, `pow_choose_two_add_mul_eq`, and
`gaussianBinomial_q_lucas`. The first three are identities in `ℕ`; the two
coefficient formulas need only a commutative ring. Complete-block, phase, and
q-Lucas statements use an integral domain, `0 < d`, and a primitive `d`th
root; q-Lucas also assumes `b,s < d`. Its exact endpoint is the evaluated-root
identity, not a named polynomial congruence modulo `Φ_d`.

`CyclotomicDivisibility.lean` has zero definitions and exactly three theorems:
`cyclotomic_exponent_eq_one_iff`,
`cyclotomic_dvd_gaussianBinomial_iff`, and
`gaussianBinomial_mul_isPrimitiveRoot`. Carry and divisibility require
`k ≤ n` and `0 < d`, with the divisibility equivalence specifically in
`ℚ[X]`. The multiple-index root value is over a commutative integral domain
and requires `0 < n`. These results plus the earlier exponent bound prove the
squarefreeness row, but no separately named squarefree theorem exists. The
Babbage-derivative row is Partial: the value is formalized, the derivative is
not.

`QCatalan.lean` has the one definition `qCatalan` and exactly eleven theorems:
`map_qInt`, `qInt_X_monic`, `qInt_X_natDegree`, `X_sub_one_mul_qInt`,
`qInt_X_eq_prod_cyclotomic`, `qInt_X_dvd_gaussianBinomial_rat`,
`qInt_X_dvd_gaussianBinomial_int`, `qInt_X_mul_qCatalan`,
`qCatalan_natDegree`, `qCatalan_eval_one_mul`, and `qCatalan_eval_one`.
Functoriality is semiring-level; monicity and degree use a nontrivial
commutative ring. The noncomputable `divByMonic` quotient in `ℤ[X]` is defined
for every `n`, including zero, has degree `n(n-1)`, and evaluates at one to the
Catalan number. No coefficient nonnegativity or unimodality is asserted.

`NewtonInterpolation.lean` has the two definitions `newtonCoeff` and
`newtonInterpolant` and exactly thirteen theorems: `newtonCoeff_eq`,
`newtonCoeff_zero`, `newtonCoeff_mul_prod`, `newtonPoly_succ`,
`eval_newtonPoly`, `degree_newtonPoly_lt`, `newtonPoly_eq_interpolate`,
`eq_newtonPoly_of_eval_eq`, `coeff_newtonPoly_self`, `newtonCoeff_eq_sum`,
`nodal_range_pow`, `prod_erase_pow_sub_pow`, and
`newtonCoeff_pow_eq_sum`. This is finite interpolation over a field.
Evaluation assumes the relevant earlier-node difference product is nonzero;
uniqueness and divided differences assume finite-range injectivity. The
geometric basis assumes `q ≠ 0`, and its coefficient sum assumes injectivity
of `j ↦ q^j`. The name `newtonInterpolant` preserves the established
scalar-sequence `Fabius.newtonPoly` API. No topology or convergence is used.

`QBetaIntegral.lean` has the total real definition `qBeta` and exactly eight
theorems: `qNumber_pos`, `qBeta_term_eq`, `qBeta_eq_prod`,
`qBeta_eq_qGamma`, `qBeta_comm`, `qBeta_pos`, `qBeta_add_one_left`, and
`qBeta_add_one_right`. Product and q-gamma evaluation, symmetry, positivity,
and both recurrences assume `0 < q < 1` and `x,y > 0`; term cancellation
assumes `y > 0` with arbitrary real `x`. No complex continuation or classical
limit is formalized.

These six modules promote seven forward rows from None to Exact: the root
block, squarefreeness, q-Catalan, q-beta evaluation, q-beta recurrence,
geometric Newton, and its triangular corollary. Q-Lucas and the Babbage
derivative move from None to Partial for the exact boundaries above. Thus the
282-row ledger is 80 Exact / 86 Partial / 108 None / 8 N/A.

The live audit across the facade is exactly 665 modules and 8,819 public
declarations. The Exponents TeX contains these semantic-union crosswalk
additions, but its retained 238-page PDF predates them and remains
rebuild-pending.
