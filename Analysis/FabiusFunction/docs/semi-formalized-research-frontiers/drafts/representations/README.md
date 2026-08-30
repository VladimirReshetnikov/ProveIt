# Representations

New standalone intake members:

- [`fabius_iterates_nowhere_analytic/`](fabius_iterates_nowhere_analytic/),
  *Nowhere Analyticity of Every Positive Compositional Iterate of the Fabius
  Function* (20 A4 pp, 1398 source lines; with a 469-line numerical
  diagnostic), arrived on 2026-08-30 with all 14 submitted payload checksums
  verified. The repaired package has an exhaustive 15-entry live ledger; the
  single CSV entry was refreshed after deterministic LF normalization. A
  Faà di Bruno partition defect, two-spine expansion,
  strict weight-unimodality argument, and Thue--Morse binary-transition lemma
  yield the manuscript's claimed nowhere-analyticity theorem for every
  positive self-composition, together with a co-countable dense zero-radius
  set.  This is primarily a derivative/composition representation result,
  rather than a new Thue--Morse atlas member.  The `n = 1` case and the
  inverse/non-elementarity infrastructure already exist in Lean; the
  `n ≥ 2` theorem appears genuinely new and remains unformalized.  The report
  has 14 nonconjectural labelled results, two explicit quarantine warnings,
  and one live conjecture.
  A hostile
  post-intake proof pass found no fatal gap and made three proof-exposition
  repairs: an explicit uniform estimate in the weighted-defect decay, the
  correct neighborhood for the outer function in the two-spine lemma, and an
  empty-union-safe definition of the `n = 1` tie set.  It also corrected the
  landing source map's nonexistent `StrictMonotonicity.lean` to the live
  `Monotonicity.lean`. Three direct `pdflatex` passes then rebuilt a clean
  canonical A4/27 mm/Libertinus 20-page PDF with no Type 3 fonts, and every
  page was rendered again. The shipped command also
  reproduced all six numerical outputs byte-for-byte in a recovered,
  fully-pinned Ubuntu/Python environment.  The companion
  [`REPOSITORY_AUDIT.md`](fabius_iterates_nowhere_analytic/REPOSITORY_AUDIT.md)
  records that environment, the output hashes, the cross-platform drift, and
  the remaining reproducibility limitations.  Two conjecture labels are
  quarantined rather than treated as open: the proposed Taylor-series
  “trichotomy” is nonexclusive at an `n = 1` interior dyadic point unless its
  third class excludes eventually-zero polynomial series, while the
  tie-cancellation statement follows from the canonical quarter-point facts
  and the report's own binary-transition lemma.  The floating-point/FFT
  diagnostic also does not substantiate the manuscript's separate claim of
  symbolic verification.  None of the manuscript or numerical labels elevate
  a result to Lean status.
- [`Fabius_Rvachev_Shape_Divisibility_Stein_Geometry/`](Fabius_Rvachev_Shape_Divisibility_Stein_Geometry/),
  *Shape, Divisibility, and Stein Geometry of the Fabius--Rvachev Law*
  (34 A4 pp, 2080 source lines; with a 466-line numerical experiment),
  arrived on 2026-08-30 with all 14 submitted payload checksums
  verified; three CSV entries were then refreshed after repository-mandated
  LF normalization. Its strict log-concavity and reliability consequences,
  convolution-rootlessness, exact scalar Stein calculus, weighted invariant
  diffusion, Legendre formal-jet rigidity, and endpoint bounds form a
  probability/representation layer. The strictness, rootlessness, diffusion,
  and Legendre-jet strands are distinct, while the scalar Stein kernel,
  Bell-moment, shape-conjecture, and endpoint material substantially overlaps
  `Fabius_Stein_Koopman_Frontier_Report/`; both remain separate pending a
  claim-by-claim editorial merge. Its claim of repository-distinctness is
  therefore stale: that earlier report already gives the same exact kernel
  values, rationality and mean identities, and proves a stronger two-term
  Lambert-periodic endpoint theorem than this intake leaves conjectural. The
  original bespoke 50-page Letter/Latin-Modern/Type-3 rendering is retained in
  repository history. The repaired title-derived pair uses canonical
  A4/27 mm/Libertinus styling and PNG plot companions; three `pdflatex` passes
  produced a 34-page PDF with embedded/subset fonts, no Type 3 font, and a
  verified 18-entry live ledger. The exact existing Lean inputs are
  crosswalked separately from the report's paper-only proposed results;
  manuscript theorem labels do not establish Lean status.
- [`Fabius_Rvachev_Noncommutative_Frontiers/`](Fabius_Rvachev_Noncommutative_Frontiers/),
  *Noncommutative Cumulant Frontiers for the Fabius--Rvachev Law* (26 A4 pp,
  1336 source lines; with a 667-line experiment), arrived on 2026-08-30 with
  all 21 payload checksums verified. The repository repair gives the report title-derived source/PDF
  stems, canonical A4/27 mm/Libertinus styling, deterministic LF CSV output,
  PNG figure selection, a three-pass build, and a verified 21-entry live
  ledger; every font is embedded and subset and the report has no Type 3 font.
  Its free and
  Boolean cumulants, exact non-free-infinite-divisibility certificates,
  q-parametric Hankel obstruction, Jacobi stripping and increment program,
  finite-sinc cumulant transfer, and inverse-Fabius/Legendre/endpoint bridges
  form a distinct representation layer with spectral-arithmetic cross-links.
  The original 29-page Letter/Type-3 rendering remains recoverable from the
  recorded arrival commit and archive SHA-256.
- [`Fabius_Rvachev_New_Frontiers-2/`](Fabius_Rvachev_New_Frontiers-2/),
  *Fabius--Rvachev New Frontiers* (36 A4 pp, 2579 source lines), arrived on 2026-08-30
  from a rootless archive with all 15 arrival payload checksums verified. The
  normalized package adds five PNG companions and embeds them to keep the
  report PDF free of the vector plots' Type 3 fonts. Its current canonical
  A4/Libertinus build is 36 pages with a verified 20-entry live ledger. The
  merged report records the exact Lean boundary: scalar-base-change
  Gram--Stieltjes naturality, all-degree rational native Jacobi coefficients,
  the polynomial Gram/Hankel determinant transport, and its Legendre up-law
  determinant and zero-based Jacobi cross-ratio specialization are formalized.
  Finite Gaunt/Wigner entry expansions, rationality by that route, roots,
  Christoffel products, quadrature, Padé identification, and asymptotics remain
  outside that tranche. Its native up-law
  orthogonal polynomials, Jacobi and Christoffel reconstruction, rational
  limits and products for pi, Gauss--Pade structure, and Legendre--Gaunt
  determinants extend the moment, transform, and representation theme. It is
  distinct from the homonymous historical report already absorbed into
  `Frontier_Compilations/`. Its original novelty screen overstated the gap:
  the pinned representation frontier already contained the Nevai-limit,
  J-fraction, Hankel, and Gauss--Padé program.
- [`Fabius_Stein_Koopman_Frontier_Report/`](Fabius_Stein_Koopman_Frontier_Report/),
  *Dyadic Stein--Koopman and q-Oscillator Calculus for the Fabius--Rvachev
  Law* (32 pp), arrived on 2026-08-30 with all 20 payload checksums verified.
  Its Appell eigenmodes, transfer determinants, q-Weyl calculus, Stein and
  Poisson operators, martingales, nonreversibility certificate, scalar Stein
  kernel, and endpoint asymptotics extend the operator-representation theme.

All five remain standalone pending claim-by-claim Lean crosswalk and deliberate
consolidation; paper theorem labels do not by themselves assert Lean status.

Series and orthogonal-expansion representations of the up-function,
consolidated (2026-08-28) into the single volume
[`Representation_Frontiers/`](Representation_Frontiers/) (299 pp;
eight parts):

- **Part I** — *Resolvent, Continued-Fraction, and Transform
  Representations of the Fabius–Rvachev System* (Jacobi coefficients,
  exact even moments, resolvent and logarithmic-derivative identities;
  formerly
  `Fabius_Rvachev_Representation_Frontiers/`);
- **Part II** — *Representation Atlas and New Analytic Bridges for the
  Fabius Function, Rvachev's Up-Function, and Their Fourier Images*
  (formerly `fabius_rvachev_representation_frontier/`);
- **Part III** — *Dyadic Multiresolution and Product–Series
  Representations* (rational mass arrays, Haar–Schauder expansions,
  Walsh–Thue–Morse products, beta-mixture limits, Bell–Bernoulli scale
  energies, inverse-quantile duality; formerly
  `Fabius_Rvachev_Multiresolution_Report/`);
- **Part IV** — *Integral, Series, Product, and Operator
  Representations* (Fredholm, exterior-power, total-positivity,
  heat-kernel, and Mellin–Barnes bridges; formerly
  `fabius_rvachev_report_package/`);
- **Part V** — *Polyphase, Operator, and Jump-Measure Representations*
  (formerly `Fabius_Rvachev_Polyphase_Representation_Report/`);
- **Part VI** — *Sampling, Padé, Mellin, Resolvent, and
  Product–Integral Representations* (formerly
  `Fabius_Rvachev_Thue_Morse_Representation_Frontiers/`);
- **Part VII** — *Unit-Circle, Bessel, and Spectral–Monodromy
  Representations* (formerly `rvachev_fabius_representations_2026/`);
- **Part VIII** — *Dyadic Multiresolution and Sampling Frontiers*
  (formerly `Fabius_Rvachev_Multiresolution_Representations/`).

(The random-variable representation is formalized in
`ProbabilityRepresentation.lean`, and `RandomSeriesLaw.lean` identifies the
unit-interval law with the affine image of the up measure.
`MeasureCauchyTransform.lean` supplies the reusable finite-measure foundation:
oriented transforms and every kernel power, affine pushforward naturality,
holomorphy off complexified support, and transform/power recurrences for an
arbitrary uniform affine fixed-point law.  Its invariant carrier needs no
topological or measurable structure and the law need not be normalized.
`MeasureCauchyMomentLaurent.lean` supplies the complementary bounded-measure
Laurent layer with exactly one public definition and fifteen public theorems.
For a finite real measure, arbitrary `{𝕜} [RCLike 𝕜]`, center `c`, and
almost-everywhere relative-ball bound `‖(x : 𝕜) - c‖ ≤ R`, its direct API
assumes `0 ≤ R < ‖z - c‖` and gives the centered moments, kernel and remainder
integrability, the exact finite Laurent identity, the mass-scaled moment bound,
the sharp geometric remainder
`μ.real univ * (‖z-c‖-R)⁻¹ * (R/‖z-c‖)^N`, and
`Summable`/`tsum`/`HasSum` convergence, together with complex wrappers for the
named oriented transform.  The existing up-specific real and complex Laurent
results are the `c = 0`, `R = 1` specialization.  The compatibility theorems
`ae_norm_sub_zero_le_one_rvachevMeasure` and
`measureCauchyMoment_rvachevMeasure_zero` respectively discharge its support
hypothesis and identify its coefficients with `upMoment`.  This Laurent tranche
does not formalize the coefficient recursion or a moment-determinacy/uniqueness
argument.
`GeometricUniformCauchy.lean` specializes this calculus to every real
`|q| < 1`; its divided DDE and adjacent-power hierarchy assume only `q ≠ 0`
and include negative ratios.  `CauchyTransform.lean` defines the canonical
unit and centered transforms and powers, proves their measure/density forms,
slit-domain calculus, transform and all-power affine bridges, the direct named
unit equation `S'(z) = 4(S(2z) - S(2z - 1))`, and both complex-slit
adjacent-power recurrences.  `CauchyCDF.lean`, `CauchySurvival.lean`, and
`CauchyHigherPowers.lean` give atom-exact CDF/survival integration by parts at
every positive kernel power.  `CauchyRenormalization.lean` proves the centered
DDE and exact all-order finite Thue--Morse derivative orbit.

The merged Stieltjes layer also proves the real logarithmic fixed point and
positive integer hierarchy for `z > 1`, real order lowering for `α > 1`,
real and complex exterior Laurent series with exact remainders, finite-height
Herglotz--Poisson formulas, integrated interval Stieltjes--Perron inversion,
and initial exact Jacobi data.  These are direct named results, not evidence
for the still-open complex logarithmic continuation, complex order,
pointwise/nontangential Sokhotski--Plemelj and principal-value Hilbert formulas,
or complete J-fraction/Padé convergence and Jacobi asymptotics.  The separate
conversion of the Thue--Morse derivative orbit into one explicit all-order
higher-kernel formula also remains open.)

The finite moment layer now has both a reusable and a Fabius-specific form.
`FiniteMomentGram.lean`, `GramStieltjes.lean`, and
`FiniteMomentJacobi.lean` provide measure-free commutative-ring/field Hankel,
normalized Gram--Stieltjes, and the complete finite Jacobi recurrence,
including its degree-zero base equation.
`OrthogonalPolynomialGramBridge.lean` proves that the up-moment functional is
integration against the canonical up measure and identifies the generic
matrix, determinant, fraction-free polynomial, and monic normalization with
their up-specific counterparts.
`MomentHankelMatrix.lean`, `MomentHankelValues.lean`, and the
`OrthogonalPolynomial*.lean` modules separately prove up-measure positivity,
the monic orthogonal construction, parity, the symmetric three-term
recurrence, and the first exact Jacobi data.  Roots and quadrature,
second-kind polynomials, finite/infinite continued-fraction identification,
and analytic convergence remain open.

`PolynomialMomentGramDeterminant.lean` now supplies the exhaustive generic
polynomial-basis transport surface: definitions `polynomialCoefficientMatrix`
and `polynomialMomentGramMatrix`, and theorems
`polynomialCoefficientMatrix_apply`, `polynomialMomentGramMatrix_apply`,
`polynomialMomentGramMatrix_eq_transpose_mul_hankel_mul`,
`polynomialMomentGramMatrix_det_eq_coefficient_det_sq_mul`,
`polynomialCoefficientMatrix_det_eq_prod_coeff`,
`polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul`, and
`gramStieltjesJacobiSubdiagonal_eq_polynomialMomentGramMatrix_det_ratio`.
The degree-coherent family hypothesis is `natDegree (p k) ≤ k`; the matrix
identity is over a commutative semiring, determinant transport over a
commutative ring, and the final field-level ratio also requires every diagonal
coefficient to be nonzero.  It requires no Hankel nonvanishing and asserts no
measure, positivity, orthogonality, root, quadrature, continued-fraction, or
convergence result.

`FabiusLegendreHankelDeterminant.lean` specializes that transport with the
exhaustive definitions `upLegendreGramMatrix`, `upLegendreGramDet` and
theorems `upLegendreGramMatrix_apply_eq_integral`,
`upLegendreGramDet_eq_prod_leadingCoeff_sq_mul_hankelDet`,
`upLegendreGramDet_zero`, `upLegendreGramDet_pos`,
`coeff_legendrePolynomial_self_div_succ`,
`gramStieltjesJacobiSubdiagonal_upMoment_eq_upLegendreGramDet_ratio`, and
`rvachevJacobiSubdiagonalRat_cast_eq_upLegendreGramDet_ratio`.  The determinant
identity and up-moment cross-ratio need only `BoundedFabius`; entry integration,
positivity, and the rational-cast ratio additionally need `IsFabius`.  The
subdiagonal index is zero-based (`beta_(n+1)`).  Finite Gaunt/Wigner entry
expansions, Christoffel reconstruction, roots, quadrature, infinite Jacobi
products/continued fractions, and asymptotics remain outside this module.

The reciprocal-Gamma portion of Part II is now formal at source checkpoint
`71ab6f6728fceb753c88d8b0573077a59acf2682`.  The reusable convergence engine
is `ScaledInfiniteProducts.lean`; `GeometricReciprocalGamma.lean` constructs
the entire product
`G_q(z) = product_n Gamma(1 + q^n z)^(-1)` for complex `q` with `‖q‖ < 1`,
proves its Mahler equation, zero orbit, reflection, and dyadic Rvachev bridge;
and `DyadicGammaOrder.lean` proves the exact negative-integer zero set and
dyadic zero/pole orders.  The Gamma-side functions are totalized pointwise
inverses, with poles recorded by negative meromorphic order.  Still open are
the raw Gamma tprod away from its poles, arithmetic canonical regrouping,
logarithmic/digamma/Malmsten/heat/integral identities, D-finiteness,
general-base pole orders, and the reciprocal-Gamma derivative coefficient
needed by the separate Thue--Morse tower.

That paragraph is retained as the historical
`71ab6f6728fceb753c88d8b0573077a59acf2682` boundary.  The current overlay pins
the next tranche to `0ba35abd4`: the five public declarations of
`ReciprocalGammaJets.lean` are `deriv_Gamma_inv_neg_nat`,
`hasDerivAt_Gamma_inv_neg_nat`, `hasDerivAt_Gamma_inv_zero`,
`analyticOrderAt_Gamma_inv_neg_nat`, and `tendsto_Gamma_inv_div_add_nat`.
They establish the exact first jet, simple analytic order, and punctured local
coefficient of the entire reciprocal Gamma function at every nonpositive
integer, without assigning a derivative to raw Gamma at a pole.

The first eight public declarations of `ThueMorseGammaTower.lean` at that commit
are `hasDerivAt_dirichletMellinContinuation_neg_nat`,
`deriv_dirichletMellinContinuation_neg_nat`, `thueMorseGammaLog`,
`thueMorseGammaTower`, `thueMorseGammaLog_eq_mellin`,
`thueMorseGammaLog_eq_integral`, `thueMorseGammaLog_dyadic`, and
`thueMorseGammaTower_dyadic`; the current integrated tree adds
`ofReal_exp_mpLimit_eq_gammaTower_div` as the ninth.  Their definitions are
total for every real parameter, while the Mellin, integral, dyadic, and ratio
theorems use positive parameters.  GammaLog is a chosen derivative coordinate,
not a proved `Complex.log` identity.  Only the parameter differential/iterated
ladder remains open within this tower; the raw Gamma tprod, arithmetic
canonical regrouping, Gamma-product logarithmic/digamma/Malmsten/heat-trace
identities, D-finiteness, and general-base pole orders remain separate
frontiers.

The mathematical bodies of the member drafts were preserved (labels,
citation keys, and asset paths were mechanically prefixed per part),
with top-level counters and reproduction instructions adapted to the
consolidated layout. Their standalone TeX/PDF pairs were deleted;
provenance with SHA-256 hashes is recorded in the volume itself, and git
history is the archive. Reproducibility files remain under the volume's
`assets/` directory, with each former package's README updated for its
new location.

Parts IV–VIII arrived 2026-08-28 as the five second-wave reports,
were first consolidated into an interim companion volume
(`Representation_Second_Wave/`, 183 pp), and were folded into the
main volume as Parts IV–VIII the same day.  The fold repaired a
rendering defect of the interim volume (its parts after the first
were numbered with `\appendix` letters running across part
boundaries, so sections collided as E–T/A–C/D–…; per-part arabic
numbering is now restored), restored the members' full part titles
(the interim volume had abbreviated three of them to one word), and
deduplicated colliding macro definitions between the waves; every
editorial intervention is marked `% ed.:` in the source.  Same
content-preserving discipline as the per-part merges; absorbed
member directories and the interim volume deleted, provenance with
SHA-256 for all eight sources in the volume's front matter.

The two fourth-wave polynomial-representation drafts (2026-08-28) were
merged the same day into the volume
[`Up_Polynomial_Synthesis/`](Up_Polynomial_Synthesis/) (*Exact
Polynomial Synthesis from Rvachev Up-Atoms*, 23 pp): the common-scale
dictionary construction (formerly
`Rvachev_Up_Polynomial_Representation_Package/`, *Exact Polynomial
Synthesis by Finite Rvachev Up-Function Dictionaries*) and the
antiderivative-train window construction (formerly
`rvachev_up_polynomial_representation/`, *Exact Polynomial Windows from
Finite Sums of Shifted and Scaled Rvachev up Functions*).  Unlike the
mechanical merges above, this is an editorial consolidation: shared
foundations stated once, the two constructions compared, the minimal
atom count sharpened to `N_d <= d+2`, and the canonical defect
identified with the shifted-quadrature first failure of the
`Dyadic_Comb_Frontiers` volume (exact special values via the spectral
Dirichlet values `D(2r)`).  A third source, the seventh-wave draft
`Rvachev_Up_Exact_Polynomial_Representation_Report/` (*Exact
Polynomial Plateaux from Rvachev's Up-Function*), was absorbed the
same day as the oversampled-lattice chapter: twisted Poisson
summation, exact reproduction order `v_2(m)` at radius-to-spacing
ratio `m` with the general-ratio defect series, the physical-scale
interval algorithm (`O(d)`-element description, `(2m+1)`-local
evaluation, full endpoint-jet matching), ghost-atom antiderivative
calculus, the exact Thue–Morse dyadic derivative stencil (convolution
inverse of the ladder's binary-partition weights), finite sinc-prefix
generators with the exact cumulant truncation law, and
odd-denominator cumulant arithmetic; its rational-arithmetic
verification package lives under
`assets/Rvachev_Up_Exact_Polynomial_Representation_Report/`.
Absorbed directories deleted; provenance with SHA-256 in the volume's
Appendix B and `assets/SHA256SUMS-absorbed.txt`.
The focused-build `CompositeMeshSharpness.lean` module now certifies the
natural-mesh universal slice of the sharp order statement: exactness for the
whole polynomial space through degree `d` is equivalent to `d <= v_2(M)`, or
to `2^d | M`; `2^d` is least, and `4^N` is least for the complete degree-`2N`
space.  This is not a minimality result for one target polynomial, Legendre
mode, or partial sum.

Six same-question Lagrange-loop reconstruction reports landed on 2026-08-29
and remain separate pending a deliberate fold into
[`Up_Polynomial_Synthesis/`](Up_Polynomial_Synthesis/):
`rvachev_lagrange_loop_report/`, `Lagrange_Rvachev_Loop_Package/`,
`lagrange_rvachev_loop_report_v3/`,
`Lagrange_Rvachev_Closed_Loop_Report/`,
`Rvachev_Lagrange_Loop_Report_v5/`,
and `Rvachev_Lagrange_Loop_Report_v6/`.
The v6 member was delivered as a bare TeX file; its rendered landing notes
record the missing companion assets and the absence of a declaration-level
Lean crosswalk.

[`Legendre_Rvachev_Self_Reconstruction/`](Legendre_Rvachev_Self_Reconstruction/)
(*Legendre--Rvachev
Self-Reconstruction on [-1,1]*) landed 2026-08-29 and is **pending
merge into `Up_Polynomial_Synthesis/`**.  It is not a seventh
Lagrange-loop sibling: the six loop reports synthesize *Lagrange
cardinals* from shifted up-atoms, whereas this one turns the Legendre
strand inward, onto the self-reconstruction and energy structure of up
itself.  Its own `CORPUS_AUDIT.md` names
`lagrange_rvachev_loop_report_v3/` as the directly preceding
Legendre-aware report and lists what it imports rather than claims.
New here: exact orthogonality of the finite self-translate blocks,
Pythagorean tails and a Sobolev energy hierarchy, a positive rational
series and an infinite-sinc integral for the energy constant
`A_2 = int_0^1 F^2`, interlevel null trains with a quarter-grid lifting
decomposition, Hilbert--Schmidt identities for the even-projector
factorization, and a sharp central-coefficient root law.  Its
theorem-level checks are exact rational with residual `0`; the reported
energy value is a stabilized display of an exact partial sum, not a
certified enclosure of the limit, and the report says so.  This is a
checksum-verified 22-file package with a 31-page Libertinus rebuild and exactly
2204 source lines, exact data certificates, four dual-format figures, and snapshot
`faa3a9b94ac0e71abdc53c36fdf428222e4d2a8c`.
Its checksum ledger was refreshed after the 2026-08-30 parity render and all
21 entries verify.
Subsequent Lean module `FabiusLegendreEnergy.lean` now defines the
polynomial-form blocks `B_n = u_n*P_(2n)` and proves exactly their complete
orthogonality, the coefficient Parseval identity, the shifted coefficient-tail
identity in both `HasSum` and `tsum` forms, and the real-variable Legendre
series for `A_2`.  At compiled checkpoint `9d5f41c2c`, the subsequent
`FabiusLegendreRationalEnergy.lean` adds the three executable definitions
`canonicalRvachevLegendreCoefficientRat`, `fabiusSquareEnergyTermRat`, and
`fabiusSquareEnergyPartialSumRat`.  Its fifteen public theorems are
`canonicalRvachevLegendreCoefficientRat_cast`,
`canonicalRvachevLegendreCoefficientRat_zero`,
`fabiusSquareEnergyTermRat_cast`, `fabiusSquareEnergyTermRat_nonneg`,
`fabiusSquareEnergyTermRat_zero`, `fabiusSquareEnergyPartialSumRat_cast`,
`monotone_fabiusSquareEnergyPartialSumRat`,
`fabiusSquareEnergyPartialSumRat_pos`,
`fabiusSquareEnergyPartialSumRat_zero`,
`fabiusSquareEnergyPartialSumRat_one`,
`fabiusSquareEnergyPartialSumRat_two`,
`fabiusSquareEnergyPartialSumRat_three`,
`hasSum_fabiusSquareEnergy_ratCast`,
`fabiusSquareEnergy_eq_tsum_ratCast`, and
`tendsto_fabiusSquareEnergyPartialSumRat_cast`.  Thus every energy partial sum
has a positive rational representative, the rational sequence is monotone,
and its real casts converge to `A_2`.  The report's four displayed cutoffs
`N = 0, 1, 2, 3` are certified exactly as `1/4`, `7/18`, `3271/8100`, and
`3246043/8037225`.

At compiled checkpoint `b9b240bc0`, the further
`FabiusSquareEnergyFourier.lean` exports no definitions and exactly four
theorems:
`integral_norm_sq_rvachevFourier_eq_two_mul_fabiusSquareEnergy`,
`fabiusSquareEnergy_eq_integral_Ioi_norm_sq_rvachevFourier`,
`fabiusSquareEnergy_eq_integral_Ioi_tprod_sinc_sq`, and
`fabiusSquareEnergy_eq_scaled_integral_Ioi_tprod_sinc_sq`.  They identify the
full real-axis squared Fourier mass with twice `A_2`, the positive-half-line
mass with `A_2`, and certify the report's Fourier-product and infinite-sinc
integrals with their exact normalizations and index ranges.

At compiled source checkpoint `a3854643d`, `RvachevMomentAppell.lean` exports six
public definitions: `rvachevRawMomentRat`, `rvachevReciprocalMomentRat`,
`rvachevAppellPolynomialRat`, `rvachevAppellPolynomial`, and
`rvachevDeconvolvedPolynomial`, together with
`rvachevDeconvolutionLinearMap`.  Its thirty public theorems are
`rvachevRawMomentRat_zero`, `rvachevRawMomentRat_even`,
`rvachevRawMomentRat_odd`, `rvachevReciprocalMomentRat_zero`,
`binomialConv_rvachevRawMomentRat_reciprocal`,
`rvachevReciprocalMomentRat_eq_completeBellPolynomial`,
`monic_rvachevAppellPolynomialRat`,
`natDegree_rvachevAppellPolynomialRat`,
`rvachevAppellPolynomial_eq_poly_cast`,
`monic_rvachevAppellPolynomial`, `natDegree_rvachevAppellPolynomial`,
`eval_rvachevAppellPolynomial_add`,
`integral_pow_mul_rvachev_eq_rvachevRawMomentRat_cast`,
`integral_eval_rvachevAppellPolynomial_add_mul_rvachev`,
`rvachevDeconvolutionLinearMap_apply`,
`rvachevDeconvolvedPolynomial_zero`,
`rvachevDeconvolvedPolynomial_add`,
`rvachevDeconvolvedPolynomial_smul`,
`rvachevDeconvolvedPolynomial_finsetSum`,
`rvachevDeconvolvedPolynomial_C_mul`,
`rvachevDeconvolvedPolynomial_monomial`,
`rvachevDeconvolvedPolynomial_X_pow`,
`coeff_rvachevDeconvolvedPolynomial_natDegree`,
`natDegree_rvachevDeconvolvedPolynomial_le`,
`natDegree_rvachevDeconvolvedPolynomial`,
`leadingCoeff_rvachevDeconvolvedPolynomial`,
`rvachevDeconvolvedPolynomial_eq_zero_iff`,
`rvachevDeconvolutionLinearMap_injective`,
`rvachevDeconvolvedPolynomial_injective`, and
`integral_eval_rvachevDeconvolvedPolynomial_add_mul_rvachev`.  This is the
exact rational raw-moment, formal reciprocal/Bell, reciprocal-moment Appell,
and polynomial-smoothing/deconvolution foundation used by the report.  The
deconvolution is now packaged as a real linear map, preserves zero, addition,
scalar multiplication, finite sums, and multiplication by constant
polynomials, and sends a monomial and `X^n` to the correspondingly scaled and
unscaled Rvachev--Appell polynomial.  Its triangular top term is exact: it
preserves the coefficient in the original `natDegree`, exact `natDegree`, and
`leadingCoeff`; its kernel is trivial; and both the packaged linear map and
the underlying raw operation are injective.

At compiled checkpoint `a3854643d`, `RvachevPolynomialSynthesis.lean` exports
no public definitions and exactly four public theorems:
`tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
`normalized_tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
`sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`, and
`normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`.
They prove the global raw and normalized sums for every nonzero natural mesh
`M` with `deg P ≤ v₂(M)`, and on `[-1,1]` the exact finite open-index form
`-2M < k < 2M`.

The focused-build `CompositeMeshSharpness.lean` module exports one public
definition, `rvachevCombExactThrough`, and seven public theorems:
`exists_shift_tsum_shifted_monomial_ne_integral_nat_real`,
`rvachevCombExactThrough_iff_padicValNat`,
`rvachevCombExactThrough_iff_pow_two_dvd`,
`rvachevCombExactThrough_two_pow`,
`two_pow_le_of_rvachevCombExactThrough`,
`isLeast_rvachevCombExactThrough`, and
`isLeast_rvachevCombExactThrough_even`.  It classifies universal exactness at
every real shift for the whole real polynomial space through degree `d` as
`M != 0 && d <= v_2(M)`, equivalently `M != 0 && 2^d | M`; proves a real
first-defect witness in degree `v_2(M)+1`; and makes `2^d` the least such mesh,
with the complete even-degree specialization `4^N`.  It does not make an
individual Legendre polynomial or a particular `S_N` minimal on that mesh.

At compiled checkpoint `a3854643d`,
`FabiusLegendreTranslateBlocks.lean` exports six
public definitions: `rvachevLegendreDeconvolutionPolynomial`,
`rvachevLegendreScale`, `rvachevLegendreIndexSet`,
`rvachevLegendreAtomCoefficient`, `rvachevLegendreTranslateBlock`, and
`rvachevTranslateGram`.  Its seven public theorems are
`natDegree_rvachevLegendreDeconvolutionPolynomial`,
`leadingCoeff_rvachevLegendreDeconvolutionPolynomial`,
`eval_legendrePolynomial_eq_sum_rvachevUp`,
`eval_legendrePolynomial_even_eq_sum_rvachevUp`,
`rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock`,
`intervalIntegral_rvachevLegendreTranslateBlock_mul`, and
`sum_rvachevLegendreAtomCoefficient_mul_gram`.  For `Q_d = D(P_d)`, the first
two prove exact natural degree `d` and the explicit unchanged leading
coefficient `(1/2)^d * choose (2*d) d`.  The remaining theorems specialize the
finite synthesis to meshes `2^d` and `4^n`, identify each literal finite translate
block with the existing polynomial block on `[-1,1]`, and prove its complete
orthogonality and exact finite atom-Gram expansion.

At compiled checkpoint `a3854643d`, the focused-build
`FabiusLegendreTranslateSeries.lean` exports five public
definitions: `rvachevLegendrePartialSumDeconvolutionPolynomial`,
`rvachevLegendrePartialSumAtomCoefficient`,
`rvachevLegendrePartialSumTranslateBlock`,
`rvachevLegendreTranslateBlockOnInterval`, and
`rvachevLegendrePartialSumTranslateBlockOnInterval`.  Its twenty-five public
theorems are
`natDegree_rvachevLegendrePartialSumDeconvolutionPolynomial`,
`leadingCoeff_rvachevLegendrePartialSumDeconvolutionPolynomial`,
`summable_norm_rvachevLegendreTranslateBlock`,
`summable_rvachevLegendreTranslateBlock`,
`hasSum_rvachevLegendreTranslateBlock`,
`tsum_rvachevLegendreTranslateBlock`,
`rvachevLegendrePartialSumDeconvolutionPolynomial_eq_sum`,
`rvachevLegendrePartialSumAtomCoefficient_eq_sum`,
`eval_rvachevLegendrePartialSumPolynomial_eq_tsum_rvachevUp`,
`eval_rvachevLegendrePartialSumPolynomial_eq_sum_rvachevUp`,
`rvachevLegendrePartialSumTranslateBlock_eq_eval_partialSumPolynomial`,
`rvachevLegendrePartialSumTranslateBlock_eq_sum_translateBlock`,
`rvachevLegendreTranslateBlockOnInterval_apply`,
`rvachevLegendreTranslateBlockOnInterval_eq_smul`,
`summable_norm_rvachevLegendreTranslateBlockOnInterval`,
`summable_rvachevLegendreTranslateBlockOnInterval`,
`hasSum_rvachevLegendreTranslateBlock_uniform`,
`tsum_rvachevLegendreTranslateBlock_uniform`,
`rvachevLegendrePartialSumTranslateBlockOnInterval_apply`,
`rvachevLegendrePartialSumTranslateBlockOnInterval_eq_eval_partialSumPolynomial`,
`rvachevLegendrePartialSumTranslateBlockOnInterval_eq_sum`,
`tendsto_rvachevLegendrePartialSumTranslateBlockOnInterval`,
`rvachevLegendrePartialSumTranslateBlock_tendstoUniformlyOn`,
`tendsto_norm_rvachevLegendrePartialSumTranslateBlockOnInterval_sub`, and
`tendsto_rvachevLegendrePartialSumTranslateBlock`.  They certify absolute pointwise
and interval-supremum summability of the literal blocks and their pointwise and
uniform sums to `up`.  They also formalize the finite-mode formula for
`C_N = D(S_N)`, expanded common-mesh coefficients, global and finite synthesis
at mesh `4^N`, and function equality with both the polynomial partial sum and
the sum of the separately scaled blocks.  They also prove that
`C_N = D(S_N)` has exactly the `natDegree` and `leadingCoeff` of `S_N`,
including degenerate partial sums whose visible degree drops.  The bundled common-mesh partial
trains converge to `up` in `C([-1,1])`, equivalently in the interval supremum
norm; raw `TendstoUniformlyOn`, norm-error-to-zero, and pointwise corollaries
are also exported.  No convergence rate, coefficientwise limit, or uniform
convergence outside `[-1,1]` is asserted.

These five modules have public definition/theorem inventories `6/30`, `0/4`,
`1/7`, `6/7`, and `5/25`, for exactly 91 public declarations.  Universal
whole-space mesh sharpness is now certified, but target-specific minimality
for an individual Legendre mode or partial sum is not.  The modules also do
not certify analytic
reciprocal-MGF/Appell generating-series or differential-operator identities,
the displayed low reciprocal coefficients, parity and the displayed closed
forms for the deconvolved Legendre family, rationality of the atom rows,
equality of the fixed-scale and separately scaled coefficient vectors, an
unconditional `natDegree(S_N) = 2*N` theorem or nonvanishing of its top
Legendre coefficient, or the later refinement, projector, and asymptotic
layers.

Three further Legendre-closure reports landed the same day, all
**pending merge into `Up_Polynomial_Synthesis/`** and all answering the
same question from different angles:
`legendre_rvachev_closed_loop/` (*Legendre--Rvachev Biorthogonal
Closure*) carries the arithmetic — exact `u_n` to `n=80` with 2-adic
valuations, reciprocal-MGF coefficients, and exact spectral sum rules;
`Legendre_Rvachev_Closed_Loop_Report_v3/` (*Legendre Polynomials in the
Rvachev Up Dictionary*) is the widest, and the only one to study the
**root geometry** of the deconvolved Legendre polynomials, with Sturm
certificates and an explicit Favard obstruction showing the family is
orthogonal for no measure; `Legendre_Rvachev_Closed_Loop_Report_v4/`
(*A One-Scale Legendre--Rvachev Closure*) is the narrowest by design,
restricting to a single scale.  The `_v3`/`_v4` suffixes are
deliberate: those two archives share a top-level directory name.

Together with `Legendre_Rvachev_Self_Reconstruction/` these make four
same-day Legendre reports beside the six Lagrange-loop ones, so the
pending merge into `Up_Polynomial_Synthesis/` now has ten members
waiting.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and provenance.
