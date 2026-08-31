# Exponents and q-series

New standalone intake members:

- [`fabius_q_frontiers_report/`](fabius_q_frontiers_report/),
  *Parameter-Flow, Gaussian, and Large-Deviation Frontiers for the
  q-Fabius--Rvachev Family* (23 A4 pp, 1,506 source lines; with two scripts,
  four CSV tables, two captured outputs, and four PDF/PNG figure pairs),
  arrived as a bare directory in direct-arrival commit
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`; no archive or outer hash was
  supplied. Its submitted ledger covers all 20 non-ledger payloads and now
  verifies after four CSV entries were refreshed for CRLF-to-LF
  normalization. All five delivered PDFs are readable and unencrypted (27
  pages total); its main report uses embedded Type-1 Latin Modern fonts and
  remains later document-style work.

- [`Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/`](Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/),
  *Continuous-Parameter Edgeworth Theory, Large Deviations, and Quadratic
  q-Gevrey Regularity at the Fabius--Rvachev Frontier* (29 A4 pp, 1,387
  main-source lines), arrived on 2026-08-30 in direct-arrival commit
  `52179f63fe955a64508915eedaa560de9f3056da` under the bare generic wrapper
  `Fabius_Rvachev_Frontier_Report_2026-08-30-G/` and was filed under this
  title-derived collision-safe name. Its manifest covers the full delivery,
  and its 19-entry checksum ledger now verifies after three CSV rows were
  refreshed for CRLF-to-LF normalization. Its title and abstract concern
  continuous-parameter Edgeworth and deviation regimes, Lambert endpoint
  asymptotics, and quadratic-exponential Denjoy--Carleman regularity.

- [`q-series-proof-oriented-article/`](q-series-proof-oriented-article/),
  *A Proof-Oriented Guide to q-Series: Shifted Factorials, Basic
  Hypergeometric Summation, Theta Products, Partitions, Bailey Pairs, and
  Rogers--Ramanujan Theory* (39 letter-paper pp, 2,891 source lines), arrived
  as a bare TeX/PDF directory in direct-arrival commit
  `1360db6064c676f83bceb23bece5ed304dd09ce8` without an archive, outer hash,
  or ledger. The repository-generated `SHA256SUMS` covers and verifies both
  delivered files; its TeX was already LF.

- [`q_series_from_first_principles/`](q_series_from_first_principles/),
  *q-Series from First Principles: Products, Basic Hypergeometric Sums,
  Theta Functions, Partitions, Bailey Pairs, and the Rogers--Ramanujan World*
  (30 letter-paper pp, 1,548 source lines), likewise arrived as a bare
  TeX/PDF directory in direct-arrival commit
  `c167e550348bfb33b4297684100d55dfb48b8c1a` without an archive, outer hash,
  or ledger. The repository-generated `SHA256SUMS` covers and verifies both
  delivered files; its TeX was already LF.

- [`q_series_monograph/`](q_series_monograph/),
  *A Proof-Driven Guide to q-Series, Basic Hypergeometric Identities, Bailey
  Chains, and Rogers--Ramanujan Theory* (1,915 source lines), arrived as a
  source-only bare directory in direct-arrival commit
  `1f0f98390d551725fc7d2274638dbd7de86ee346` with neither PDF nor ledger.
  Intake repaired the carriage-return (CR) corruption in the intended `\rho_2`
  token at line 863 and added a one-entry repository `SHA256SUMS` for the sole
  delivered TeX. The package remains source-only: no PDF or auxiliary package
  was delivered or produced.

These five packages remain separate pending post-publication comparison,
canonical document work, and Lean crosswalks. In particular, no semantic
duplicate analysis of the three similarly scoped general q-series articles
was performed during intake, and manuscript labels or numerical checks do not
establish Lean verification.

- [`inverse_q_analogs_and_series/`](inverse_q_analogs_and_series/),
  *Inverse q-Analogs and Their Series Expansions: A Branch-Aware,
  Proof-Complete Synthesis* (85 A4 pages), is the canonical consolidation of
  the six former inverse-q and forward-expansion packages.  Its
  [`theorem_concordance.csv`](inverse_q_analogs_and_series/theorem_concordance.csv)
  accounts for all 260 source result environments, with the revision-backed
  audit validating 260/260 rows; the retained-asset checksum ledger verifies
  43/43 entries.  The
  [`PROVENANCE.md`](inverse_q_analogs_and_series/PROVENANCE.md) and
  [`assets/ASSET_DISPOSITION.csv`](inverse_q_analogs_and_series/assets/ASSET_DISPOSITION.csv)
  preserve package-, result-, archive-, and asset-level provenance.  Unique
  reproducibility assets live under `assets/`; the superseded layouts remain
  recoverable from the pinned pre-retirement Git revision and repository
  history.  The q-Pochhammer monograph remains the broad forward-theory
  reference, while `Cyclotomic_q_Fabius_Rvachev_Frontier/` retains the wider
  natural-boundary and blow-up program beyond this inverse-branch synthesis.
  The three-pass build, clean-log, metadata/font, and all-page visual
  publication gates passed on 2026-08-31.

- [`Cyclotomic_q_Fabius_Rvachev_Frontier/`](Cyclotomic_q_Fabius_Rvachev_Frontier/),
  *Cyclotomic Blow-Ups and Natural Boundaries for the q-Fabius--Rvachev Sinc
  Product* (25 pp at arrival; currently 29 A4 pp and 1,896 source lines),
  arrived on 2026-08-30 from
  `Cyclotomic_q_Fabius_Rvachev_Frontier.zip` (outer SHA-256
  `029da7d9ec96a0b2e5c4164c37f2b361dd015112bd0c6237263e3c538c5b0f64`).
  All 22 submitted payload hashes verified; five CSV entries were refreshed
  after CRLF-to-LF repository normalization. Its title and abstract place its
  radial root-of-unity expansions, claimed natural-boundary theorem,
  cyclotomic blow-ups, Bell/moment condensation, and inverse branches beside
  the consolidated q-series frontier. A post-publication revision crosswalks
  the global geometric-sinc q-Pochhammer factorization while leaving the
  cyclotomic asymptotic and natural-boundary layers manuscript-only; the
  refreshed active ledger verifies all 22 payloads. The current five PDFs have
  33 pages in total (29 main plus four one-page figures). The main report still
  uses Latin Modern rather than the house Libertinus face and retains nine
  embedded/subset Type-3 figure-font rows; the standalone figures contain nine
  more. Font normalization remains deferred.

- [`Fabius_Rvachev_Frontier_Report/`](Fabius_Rvachev_Frontier_Report/),
*Negative Parameters, Reciprocal Bases, and the Gaussian Boundary* (26 pp),
arrived on 2026-08-30 with all 13 payload checksums verified.  It develops
negative-parameter affine transport, reciprocal-base digit reversal,
multisection, shape theory, and the Gaussian boundary for geometric-uniform
laws.  Because much of that subject already appears in Part VII of the
consolidated volume, the report remains standalone until its genuinely new
claims are isolated and the overlap is deliberately deduplicated.  Paper
theorem labels do not by themselves assert Lean formalization.

- [`Fabius_Flat_Parameter_Response_Dynamics/`](Fabius_Flat_Parameter_Response_Dynamics/),
  *Flat Parameter Fronts, q-Susceptibility, and Smooth Dynamics* (26 A4 pp;
  1,944-line TeX and 519-line deterministic exact/Monte-Carlo program), was
  filed on 2026-08-30 from `fabius_frontier_report_2026.zip` (803,598 bytes;
  SHA-256
  `afdcf522589a7baad82c81a527c02dcc09e58455ab14c57a9c492e65563c647e`).
  Its immutable 13-entry arrival ledger verifies 13/13 and the exhaustive
  current ledger verifies 17/17. The pinned replay reproduced the two exact
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
three natural shifted forms, and the monograph's single shifted-central
identity for every integer shift, all over arbitrary commutative semirings.
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
reciprocity clause of the monograph's compound structure theorem, while its
separate degree and coefficient-polynomial clauses keep that full row partial.

`GaussianBinomialAtNegOne.lean` adds exactly five public theorems:
`gaussianBinomial_neg_one_even_even`,
`gaussianBinomial_neg_one_odd_even`,
`gaussianBinomial_neg_one_odd_odd`,
`finiteQPochhammerIn_neg_one_even`, and
`finiteQPochhammerIn_neg_one_odd`.  Together with
`gaussianBinomial_neg_one_even_odd_eq_zero` from the reciprocity module, these
give all four Gaussian parity values and both paired finite-product identities
over arbitrary commutative rings, without division or characteristic
restrictions.  The companion report proves the first derivative and
simple-root statement only at paper level; those polynomial-interface results
remain unformalized.

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

Member: `Exponents_and_q_Series_Frontiers`
(currently 16,234 source lines; the retained origin-main rendering is 236 A4
pages and 6,941,043 bytes). During the source-only conflict resolution the PDF
was deliberately selected from `origin/main`, not rebuilt from the merged TeX.
Accordingly, the TeX rows in the two historical asset ledgers still record the
origin-main source hash and remain stale until the next rendered rebuild. The
volume is the
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

Second member: `q_pochhammer_q_binomial_monograph/`
(212-page last validated A4 PDF; book class; the current source-only merge is
13,121 lines while the retained PDF is 1,576,424 bytes; the PDF was not
rebuilt after the merged sinc--Pochhammer crosswalk update) —
*q-Pochhammer Symbols and q-Binomial Coefficients*, a standalone
proof-oriented reference monograph on the q-machinery itself, filed
2026-08-28 per the Lambert-W precedent (a reference companion rather
than a research report, so it is kept as its own document instead of
being merged into the frontier volume).  Its corpus role: Parts II, VI,
and VII of the frontier volume, and the repository's formalized
Gaussian-binomial core, consume exactly this machinery — shifted
factorials, Gaussian coefficients with their cyclotomic structure,
q-binomial theorems, q-Gauss summation, Jacobi's triple product, theta
functions, Bailey pairs, q-Lucas congruences, q-Newton interpolation at
geometric nodes, and Bernoulli asymptotics of Gaussian coefficients all
appear in the frontier volume's q-Gaussian derivative-tower,
Stieltjes–Wigert, and q-orbit chapters, and the monograph proves each
from first principles with a formula atlas, a limit dictionary, a
proof-dependency guide, and a formalization-architecture chapter.  It
was audited on arrival (ten core theorems re-verified symbolically; the
Chern–Dilcher–Jiu deleted-singularity identity and Ramanujan's ₁ψ₁
verified numerically to 30 digits; one dominated-convergence majorant
repaired with an `% ed.:` note).

Its current formalization ledger has 248 labelled results: 42 exact, 74
partial, 129 with no counterpart, and 3 interface-only.  Within that
exhaustive total, the 191-result core in Chapters 1–23 has 36 exact, 29
partial, 123 with no counterpart, and 3 interface-only entries.  The later
Chapter 24 Fabius bridge is included in the full ledger and crosswalked
locally; its pointwise inside `q^2`-Pochhammer factorization is now formal for
every complex strict contraction, while the compound spectral theorem remains
partial at its named centered/MGF wrappers, reciprocal outside-disk clause,
and named local-uniform or normal convergence of the Pochhammer-product
right-hand side.  The algebra of
q-shifted factorials now accounts for 3 exact, 1 partial, and 11
unformalized results; the q-integer and Gaussian-coefficient chapter for
3 exact, 2 partial, and 4 unformalized results. The finite
q-binomial/inversion chapter now accounts for 9 exact, 1 partial, and 0
unformalized results; the weighted chapter for 3 exact, 2 partial, and 3
unformalized results; and the basic-hypergeometric chapter for 1 exact, 0
partial, and 8 unformalized results. The cyclotomic chapter now has 1 exact,
0 partial, and 8 unformalized results. The exact rows include the primary and
second q-Cauchy identities, both weighted-Pascal recurrences,
elementary--complete orthogonality, and weighted symmetric-function inversion.
Their adjacent strengthenings are recorded human-readably in the monograph:
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
`QBinomialReciprocity.lean` (four theorems),
`GaussianBinomialAtNegOne.lean` (five theorems), and
`RvachevPochhammerFactorization.lean` (one definition, nine theorems).
The five `GaussianBinomialAtNegOne` theorems are
`gaussianBinomial_neg_one_even_even`,
`gaussianBinomial_neg_one_odd_even`,
`gaussianBinomial_neg_one_odd_odd`,
`finiteQPochhammerIn_neg_one_even`, and
`finiteQPochhammerIn_neg_one_odd`. The first three together with the reused
`gaussianBinomial_neg_one_even_odd_eq_zero` theorem from
`QBinomialReciprocity` prove the monograph's complete `q = -1` value formula
over every commutative ring, for all natural parameters including above-row
zero extension. The `q`-Lucas theorem used by the printed proof remains
unformalized; the status promotion concerns the corollary's exact statement.
The q-difference annihilation row is exact through
`qDifference_sum_eval₂_eq_zero_of_degree_lt`, with the stronger
characteristic-polynomial, all-moment, and scalar-extension top-coefficient
results recorded alongside it. The chapter's alternating sums, both
weighted-subset conventions,
named module-valued inversion iff, and both kernel orthogonalities are exact.
Both orientations
of q-Vandermonde and both central-support presentations are exact in
`QBinomialVandermonde.lean`; the monograph's single signed shifted-central
formula is now exact for every integer shift through the zero-extended
`gaussianBinomialInt`, both as a finite natural-range sum and literally as a
finite-support `finsum` over all integers. The ledger also now records the
genuine real infinite product `qPochhammerInf` and its contractive-base
convergence/positivity layer, replacing the stale claim that every infinite
q-Pochhammer in the development was merely a finite `Finset.range` product.
The separate complex symbol now has its own contractive-nome convergence
API, and the geometric sinc product has a global spectral factorization for
every complex strict contraction with nome `q^2`; only the two final Rvachev
wrappers specialize to nome `1/4`.  The compound Chapter 24 theorem remains
partial because its named centered/MGF wrapper, outside-disk reciprocal
formula, and local-uniform/normal-convergence packaging are not all
formalized.
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
the nine theorems `Fabius.complexQPochhammerInf_eq_tprod`,
`Fabius.multipliable_one_sub_mul_pow_complex`,
`Fabius.hasProd_complexQPochhammerInf`,
`Fabius.tendsto_finiteQPochhammerIn_complex`,
`Fabius.summable_norm_sineTerm_qpow_pair`,
`Fabius.geometricSincProduct_eq_tprod_pair`,
`Fabius.geometricSincProduct_eq_tprod_complexQPochhammerInf`,
`Fabius.rvachevFourierProduct_eq_tprod_complexQPochhammerInf`, and
`Fabius.rvachevFourier_eq_tprod_complexQPochhammerInf`.  The symbol is total;
the named multipliability, product, and finite-prefix convergence theorems
require exactly `‖q‖ < 1` and allow arbitrary complex `a`.  The two dyadic
spectral theorems are the last two: they fix the scale and nome `1/4`, hold for
every complex `z` including at zero factors, and the Fourier form assumes
exactly a bounded Fabius witness satisfying `IsFabius`.  Before those
specializations, `geometricSincProduct_eq_tprod_complexQPochhammerInf` proves
globally for every complex `q,z` with `‖q‖ < 1` that
`S_q(z) = ∏'_k (z^2/(k+1)^2;q^2)_∞`; the paired-index and absolute-summability
theorems justify the exchange of scale and spectral-zero indices, including
`q = 0`, negative and nonreal contractions, and zero factors.  The
eight-theorem sinc-product tranche above
supplies the general-`q` uncentered real-frequency bridge, locally uniform
entire `S_q`, and real-frequency local and compact uniform convergence of the
full phase-bearing prefixes.  There is still no named centered or MGF
wrapper, no outside-disk reciprocal formula, and no named local-uniform or
normal-convergence theorem for the Pochhammer-product right-hand side.
