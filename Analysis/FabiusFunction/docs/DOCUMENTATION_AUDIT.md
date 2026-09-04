# Documentation audit

`AGENTS.md` lists two documentation invariants for
`Analysis/FabiusFunction/Lean`:

- every source file carries a `/-! ... -/` module header; and
- every non-`private` declaration carries a `/-- ... -/` doc comment.

Neither held corpus-wide when this audit was first run.  This file records the
gap, and
[`scripts/doc_audit.py`](../scripts/doc_audit.py) makes it measurable, so that
a reviewer can check a change did not make it worse rather than re-deriving
the numbers by hand.  `AGENTS.md` asks for exactly this: a recorded, executable
scan rather than a number quoted from a vanished shell session.

## Running it

From the repository root:

```sh
python3 Analysis/FabiusFunction/scripts/doc_audit.py
python3 Analysis/FabiusFunction/scripts/doc_audit.py --list
```

The first form prints the totals and the twenty worst files.  The second adds
every undocumented declaration as `file:line  name`, which is the form to use
when clearing one file.

To use it as a gate:

```sh
python3 Analysis/FabiusFunction/scripts/doc_audit.py \
  --baseline Analysis/FabiusFunction/docs/doc_audit_baseline.json
```

This exits non-zero if the missing-doc total rises, if any individual file gets
worse, if a new file appears without a module header, or if the corpus inventory
changes without a reviewed baseline refresh.  The ratchet was originally
needed to make progress against a large inherited backlog.  As of 2026-08-29
that backlog is zero, so the checked baseline now enforces both invariants
without an exception.

Refresh the baseline with `--write-baseline` after genuinely reducing the
missing-doc count or after verifying a fully documented corpus addition.

## What the script does and does not check

It is a lexical scan, not Lean elaboration.  It tracks nested `/- -/` blocks,
`/-- -/` doc comments, `/-! -/` module comments, string literals and `--` line
comments, so a declaration keyword appearing inside a comment or a string is
never counted.  It accepts an attribute line (`@[simp]`, a multi-line
`@[...]`), an attribute on the same line as its declaration
(`@[simp] theorem foo`), a `set_option ... in` line, or blank lines between a
doc comment and the declaration it documents.  It also accepts the one-line
`/-- ... -/ theorem foo` form.

It does not see declarations produced by macros.  A `to_additive`-generated
name is invisible to it, exactly as it is to a reader of the source, so a
generated declaration is neither counted as present nor reported as
undocumented.

It says nothing about whether a doc comment is *correct*.  That is the more
expensive audit, and three defects it would have caught are recorded below.

## Findings

### Module headers

Twelve modules had no `/-! ... -/` header at all, verified by direct grep
(`/-!` occurring zero times in the file):

`PeriodicFourier`, `PeriodicMean`, `HalfQBinomial`, `ThueMorseGenerating`,
`ThueMorsePrefix`, `FabiusSaddleCentral`, `SaddleAllOrders`,
`FabiusSaddleExponentAllOrders`, `FabiusSaddleTailAllOrders`,
`FabiusSaddleReferenceTail`, `NegativeLaplaceVerticalOrdinaryJets`,
`GammaSecondOrder`.

Four more had a bare title with at most one line of prose, and one of those
described finished, downstream-consumed results as scratch development:

`FabiusLambertDerivativeBounds`, `FabiusSaddleCentralLambert`,
`NegativeLaplaceVerticalTaylor`, `NegativeLaplaceVerticalFourthBound`.

`SaddleLogExpansionAlgebra` called itself a scratch module in an otherwise
accurate header.

All of these have been written or rewritten.  Every header was drafted against
the whole file and then checked by a second reader against the same file,
because a header that is trusted and wrong is worse than one that is absent.

`PeriodicFourier` is the case that mattered most: 72 public declarations, the
entire Mellin and Fourier analysis of the regularized Bose kernel, and no
statement anywhere in the file of what it was for.

### Doc comments

The backlog began at 862 undocumented public declarations, 31% of the corpus.
Two documentation waves and a pass over the two root modules first brought it
to 176, or 6.2%, and the original 191-module corpus was subsequently cleared
according to the then-current checker.

That apparent zero exposed a checker defect: declarations written as
`@[simp] theorem foo` on one line were not counted at all.  After teaching the
auditor to remove balanced leading attribute blocks, and after the corpus grew
to 311 modules, the corrected 2026-08-27 inventory initially contained 4,803
public declarations with 105 missing comments in 40 files.  The old parser saw
only 4,606 declarations and
36 gaps on those same bytes; the correction therefore recovered 197 attributed
declarations, including 69 undocumented ones.  Run the script for the live
numbers rather than copying these historical values.

The historical post-merge 2026-09-01 inventory contained 675 modules and 8,909
lexically visible public declarations, with zero missing module headers and
zero missing doc comments.  A fresh 2026-09-04 audit for this documentation
pass scans the semantic union of 1004 facade-reachable modules and 12,500
public declarations.  An earlier frozen upstream checkpoint contained 11,920 declarations; the
retained unconditional public
`complexQPochhammerInf_eq_qPochhammerInfIn` bridge in
`RvachevPochhammerFactorization.lean` gives the 11,921 merge-union checkpoint,
and `exists_eq_in_residual_interval` in `MeanValueBracket.lean` contributes
the second post-upstream declaration. The Bell normalization/support package
adds four declarations, repeated differential blocks add nine, the Cauchy
reflection/integral/addition package adds ten, and the reverse-row Stirling
recurrence adds one. Those later additions are included in the audited union;
this paragraph does not derive the current total by arithmetic from the older
checkpoint. This is a lexical inventory, not a claim that every
module has just been recompiled. The audit finds no missing module
header or declaration comment,
including throughout
`FabiusInverseExactDyadicModulus.lean`, `JacobiTwoSquareCount.lean`, and
`LagrangeRvachevMatrix.lean`, as well as the incoming
`GeometricRichardsonGenerating.lean`, `TwoPhiOneReversal.lean`, and
`QChuVandermonde.lean` APIs and the strengthened
`GaussianBinomialCumulants.lean` surface, and the new
`GeometricUniformRealization.lean`, `RegularCentralQBinomialSum.lean`,
`LambertWBranchGapBernoulli.lean`, `GaussianBinomialFixedColumnRate.lean`, and
`RvachevAppellHasse.lean`, `GeometricUniformMomentPolynomial.lean`,
`RvachevLagrangeNodesOnly.lean`, `GaussianBinomialGreaterOneAsymptotics.lean`,
`ThueMorseGammaTowerDifferential.lean`,
`GeometricUniformMomentPolynomialBridge.lean`,
`GeometricUniformComplexMomentProduct.lean`, `ThueMorseCornerIntegral.lean`,
`RvachevLegendreCentralSum.lean`, `HalfQBinomialRootSimplicity.lean`,
`GeometricUniformExteriorComplexMomentGerm.lean`,
`GeometricUniformMomentPolynomialDegree.lean`,
`RvachevLaurentLeading.lean`, `FinitePrefixAppellRecovery.lean`,
`GeometricUniformMomentRatFunc.lean`, `RvachevLegendreBiorthogonality.lean`,
`GeometricUniformMomentReciprocity.lean`,
`QPochhammerLambertForm.lean`, `CentralQVandermondeInfinite.lean`,
`ThueMorseNewmanSelfSimilarity.lean`, `TriangularPowerProduct.lean`,
`DyadicBoundaryIdentity.lean`, `MeanValueBracket.lean`, and
`FinitePrefixThueMorseCollapse.lean`, `ProuhetBaseTwoBridge.lean` leaves,
together with the strengthened
`ProbabilityLaplaceMoments.lean` surface,
as well as the sixteenth theorem in `FinitePolynomialFunctional.lean` and the
new `GridEvaluationCertificate.lean` and `IntegerCRTCertificate.lean` leaves,
followed by `NorlundGeneralized.lean`, `StirlingSymmetricFunctions.lean`,
`LagrangeInversionUniqueness.lean`, `NewtonReciprocal.lean`,
`StirlingSecondReverseRowIdentity.lean`, and
`TransseriesWrightOmegaTerms.lean`.
Relative to the
610/8,318 activation checkpoint, the current tree adds 393 modules and 4,167 declarations.
Relative to the earlier 630/8,552 merged checkpoint, concurrent source work
adds 373 modules and 3,933 declarations.  The post-merge 675/8,909 inventory,
the intervening 903/11,448 Lambert-series inventory, and the immediately
preceding 914/11,555 scaled-geometric and 915/11,556 real-MGF-bridge
checkpoints, together with the incoming branch's 906/11,461 complex-product
checkpoint, remain historical, not descriptions of the live facade.  In the
merged chronology, the historical complex-product checkpoint 918/11,568 was
followed by the half-base root-simplicity leaf at the merged-main pre-local
checkpoint 919/11,569, the exterior reciprocal-germ leaf at 920/11,572, and
the sharp coefficient-and-degree leaf at the historical 921/11,575
checkpoint.  The one-definition/six-theorem Laurent-leading leaf then gave
922/11,582, the eleven-definition/seventeen-theorem finite-prefix leaf gave
the historical pre-RatFunc checkpoint 923/11,610, and the one-definition/
four-theorem global RatFunc leaf gave the historical 924/11,615 checkpoint.
Two theorems added to `ProbabilityLaplaceMoments.lean` then gave 924/11,617,
and the one-definition/one-theorem Legendre--Rvachev biorthogonality leaf gave
the historical 925/11,619 checkpoint.  Later merged source work contributes
the zero-definition leaves `QPochhammerLambertForm` 0+5,
`CentralQVandermondeInfinite` 0+4, `TriangularPowerProduct` 0+2,
and `MeanValueBracket` 0+6; the 1+12 `ThueMorseNewmanSelfSimilarity` leaf; and
a net twenty-nine further declarations in existing modules.  These changes
reached the immediate pre-reciprocity checkpoint 930/11,678.  Promoting the
complex-product differentiability theorem and adding the exhaustive 1+5
reciprocity leaf add one module and seven declarations, giving the historical
reciprocity checkpoint 931/11,685.  The subsequently merged zero-definition
leaves `DyadicBoundaryIdentity` 0+2 and `FinitePrefixThueMorseCollapse` 0+8 add
two modules and ten declarations, giving the historical 933/11,695 checkpoint.
Finally, `ProuhetBaseTwoBridge` 0+6, one new theorem in
`DyadicBoundaryIdentity`, and seven new theorems in
`ThueMorseNewmanSelfSimilarity` add one module and fourteen declarations in
total, giving the historical 934/11,709 census.  Subsequent consolidated
series-and-transseries work reached the historical 943/11,791 checkpoint.
The next flatness/block tranche gave the historical 944/11,806 census.  The
sixteen-module overlay added sixteen modules with 21 definitions and 115 theorems and
24 declarations in place: `TransseriesFlat` gains 3+11 scalar-compatibility
declarations, `TransseriesDifferentialBlock` gains four theorems,
`QBinomialTheoremInfinite` gains five, and
`RvachevPochhammerFactorization` gains one.  That audited overlay checkpoint is
therefore the historical 960/11,966 census, with no missing module header or
public declaration comment.  Registering the focused-build-verified
zero-definition/eight-theorem `StirlingCompleteHomogeneous` leaf advances the
historical facade checkpoint to 961/11,974.  On the incoming branch, an
overlapping series/transseries route reached historical checkpoints
943/11,787, 952/11,881, 952/11,884, 967/12,001, 969/12,048, and
970/12,051; those receipts are not additive with the consolidated checkpoints
above.  Reconciliation produced the historical merged checkpoint 970/12,056.
The following seven-module checkpoint was 977/12,133; the two-module
certificate overlay reached 979/12,142, and the six-module successor was
985/12,199.  Adding the one-module, 34-declaration `BellSetPartitions` leaf
gives the historical 986/12,233 census.  The preceding merged inventory was
1003/12,485.  On the earlier
exterior-germ branch, the inner-complex 906/11,461 checkpoint was followed by
the branch-local 907/11,464 checkpoint; its preceding real-MGF and algebraic
moment-polynomial checkpoints were 905/11,458 and 904/11,457.  These older
branch-local counts are explicitly historical.

#### Historical incoming proof-inventory checkpoints

The incoming 16-module overlay contains 136 lexically visible public
declarations: 21 definitions and 115 theorems.  Its exhaustive module counts
are `BackwardErrorExistence` 1+6, `BellLeibnizTower` 1+5,
`CayleyTreeFunction` 1+8, `DerangementNearestInteger` 1+7,
`LambertCorrectionEquation` 2+9, `LambertShiftConcavity` 0+5,
`LeastTermIndex` 1+6, `LinLogCoreInversion` 4+18,
`OrdinaryPartialBell` 2+4, `PowerLogCoreInversion` 3+6,
`RemainderTransport` 0+3, `StaircaseInversion` 0+7,
`TouchardEulerOperator` 2+8, `TransseriesDifferentialClosure` 2+9,
`TransseriesHarmonicIncrement` 0+2, and `WrightOmega` 1+12.
`LaplaceMomentBoundsSharp` was modified in place and is not counted as a new
module.  Together with 24 in-place declarations, this produced the historical
960/11,966 checkpoint from 944/11,806.  This is an API inventory, not an
automatic promotion of wider manuscript claims.

The registered `StirlingCompleteHomogeneous` leaf is 0+8.  It identifies the
fixed-column Stirling power series with the complete-homogeneous generating
series, gives the `S(k+r,k)=h_r(1,…,k)` and finite-multiplicity formulas,
supplies `Fin k` and Mathlib `hsymm` forms, and proves denominator-cleared and
reciprocal falling-factorial normalizations.  The coefficient layer is over
commutative semirings, the power-series bridge over commutative rings, and the
falling-factorial results over fields with `x ≠ 0`; `k=0` is included and the
`n-k` form assumes exactly `k ≤ n`.  It gave the historical 961/11,974
checkpoint.

From there, nine incoming modules contribute eight definitions and sixty
theorems: `CayleyKernel` 1+14, `CayleyLocalCoordinate` 1+7,
`DivisorTransform` 2+9, `ExpSeriesRecurrence` 1+3,
`FabiusEndpointTwoTerm` 0+2, `StirlingSeriesCoefficients` 3+12,
`TransseriesBlockClasses` 0+3, `TransseriesMonomialUniqueness` 0+2, and
`WrightOmegaTwoOrders` 0+8.  Existing-module changes contributed a net
fourteen declarations: `AppellSequence` gained eleven and became 3+34,
`GaussianBinomialFixedColumnRate` transferred one theorem and became 0+9,
`RemainderTransport` gained one and became 0+4, `TransseriesWellBased` gained
two written theorems and became 0+7, and `WrightOmega` gained one and became
1+13.  The two `to_additive` names remain outside the lexical count.  This is
the historical merged 970/12,056 inventory.

The next seven modules contain eleven definitions and 69 theorems:
`AbelPolynomialSeries` 2+9, `AssociahedronFaceNumbers` 4+23,
`BernoulliFormalLog` 0+5, `ExponentialRescaling` 0+4,
`PochhammerFalling` 1+13, `RaneyNumbers` 4+12, and
`UnitSeriesPowerRecurrence` 0+3.  Three theorems now owned by
`ExponentialRescaling` were relocated from `NorlundDiagonal`, so existing
modules contribute a net minus three declarations.  The exact change is
therefore +7 modules and +77 lexical declarations, giving the historical
977/12,133 checkpoint with no documentation gap.  This census records reachability and the finite/formal or
explicit analytic statements under their source hypotheses; it does not by
itself promote any broader manuscript claim.

The two certificate leaves are exhaustively `GridEvaluationCertificate` 0+4
and `IntegerCRTCertificate` 0+5.  The grid API is
`mvPolynomial_eq_of_eval_eq_on_grid`,
`mvPolynomial_eq_of_eval_eq_on_grid_of_degreeOf_sub_le`,
`mvPolynomial_eq_of_eval_eq_on_grid_of_degreeOf_le`, and
`mvPolynomial_grid_eval_injective`; it works over any commutative integral
domain with the stated coordinatewise grid-cardinality bounds.  The integer
API is `int_prod_dvd_of_pairwise_coprime`,
`int_eq_zero_of_modEq_zero_of_natAbs_lt_prod`,
`int_eq_of_modEq_of_natAbs_sub_lt_prod`,
`int_eq_of_modEq_of_natAbs_add_lt_prod`, and
`int_eq_of_modEq_of_two_mul_natAbs_lt_prod`.  Signed composite moduli and the
empty divisibility family are included; the equality certificates retain
strict magnitude bounds.  No field, characteristic-zero, primality,
reconstruction, or probabilistic-certificate claim is made.  This is the
historical 979/12,142 checkpoint.

#### Historical 985/12,199 census

The successor adds six facade modules containing 49 public declarations:
`NorlundGeneralized` 3+18, `StirlingSymmetricFunctions` 0+4,
`LagrangeInversionUniqueness` 0+6, `NewtonReciprocal` 1+5,
`StirlingSecondReverseRowIdentity` 0+2, and
`TransseriesWrightOmegaTerms` 0+10.  Eight further public declarations enter
existing modules, so the authoritative delta from the preceding certificate
checkpoint is +6 modules and +57 declarations.  The resulting 985/12,199
census had no missing module header or public declaration comment.  This is
an API/documentation inventory under the source statements' displayed
hypotheses, not an automatic promotion of broader claims.

#### Historical 986/12,233 census

`BellSetPartitions` adds one facade module and 34 explicit public declarations
to the preceding checkpoint.  The historical 986/12,233 audit reports no
missing module header or public declaration comment.  This census update does
not by itself promote any broader manuscript claim.

#### Current 1004/12,500 census

The fetched mainline overlay and the existing feature-branch union add 18
facade-reachable modules and 267 public declarations beyond the historical
986/12,233 checkpoint.  The current source audit reports 1004 modules and
12,500 explicit public declarations, with no missing module headers or
declaration comments.

#### Consolidated transseries foundations and corrected flatness

The incoming-branch snapshot in this subsection ran from 943/11,791 to
944/11,806 by adding its vector 1+11 view of `TransseriesFlat` and three
Laurent-block theorems.  Those figures are historical and incomplete relative
to the merged union: the retained scalar compatibility API, explicit
OrderDual wrappers, later fifteen-leaf tranche, two new leaves, Appell
extension, and power-recurrence leaf are reflected in the later historical
checkpoints above.  The inventories below therefore state the semantic union, while
generated `to_additive` names remain intentionally outside the lexical count.

`TransseriesScale.lean` is exhaustively 3+6.  Its public definitions/structure
are `IsAsymptoticScale`, `poincarePartialSum`, and `IsPoincareExpansion`; its
theorems are `poincarePartialSum_zero`, `poincarePartialSum_succ`,
`IsPoincareExpansion.isLittleO_succ_remainder`,
`IsPoincareExpansion.tendsto_coeff`,
`IsPoincareExpansion.tendsto_coeff_div`, and
`IsPoincareExpansion.coeff_unique`.  The `q0:def:scale`, `q0:def:poincare`,
`q0:eq:coefficients`, and `q0:prop:uniqueness` correspondence is **Exact**.
The scale and coefficients are respectively scalar- and vector-valued over an
arbitrary normed field and filter; uniqueness alone explicitly requires the
proper-filter hypothesis `NeBot`.

`TransseriesFlat.lean` is exhaustively 4+22 in the merged union.  Its vector
core is `IsFlat`; `isFlat_zero`, `IsFlat.add`, `IsFlat.neg`, `IsFlat.sub`,
`IsFlat.const_smul`, `isFlat_exp_neg_rpow_atTop`,
`IsPoincareExpansion.add_flat`,
`IsPoincareExpansion.sub_same_coeff_isFlat`,
`IsPoincareExpansion.iff_sub_isFlat`,
`IsFlat.smul_of_scale_absorption`, and
`IsFlat.smul_of_isBigO_inv_pow`.  Its retained scalar compatibility layer is
`flatSubmodule`, `AbsorbsScale`, `powScale`; `mem_flatSubmodule_iff`,
`IsFlat.mul_absorbsScale`, `absorbsScale_const`,
`IsPoincareExpansion.add_isFlat`, `isFlat_sub_of_isPoincareExpansion`,
`isPoincareExpansion_iff_isFlat_sub`, `isPoincareExpansion_zero_iff`,
`powScale_eq_rpow`, `absorbsScale_of_isBigO_pow`, `isFlat_exp_neg`, and
`isPoincareExpansion_add_exp_neg`.  Thus `q0:def:flat` and the corrected
power-scale `q0:prop:invisible` are **Exact**: the concrete exponentially
small term, vector-space closure, preservation of coefficients, and the exact
same-coefficient iff are named.  The generic multiplier theorem assumes
explicitly that for every target `N` there is an `M` for which
`m * φ M = O(φ N)`; only the power-scale specialization derives that
absorption from an inverse-power growth estimate and eventual nonvanishing.
No polynomial-growth multiplier closure for an arbitrary asymptotic scale is
claimed.

`TransseriesWellBased.lean` has no definitions and seven lexically visible
theorems: `dickson_isPWO`, `dickson_antichain_finite`, `dickson_isPWO_pi`,
`neumann_isPWO`, `neumann_finite_factorizations`,
`neumann_isPWO_orderDual`, and `neumann_finite_factorizations_orderDual`.
The multiplicative theorems also
generate the public additive names `neumann_add_isPWO` and
`neumann_finite_decompositions`, which the audit does not count.  The
`q0:lem:dickson` and `q0:lem:neumann` statuses are **Exact**.  The explicit
wrappers state the manuscript orientation; over a partial order the precise
claim is `Set.IsPWO` on `OrderDual`, not a greatest-element characterization.

`TransseriesPolyLogScale.lean` has no definitions and four theorems:
`isLittleO_plMonomial`, `isAsymptoticScale_plMonomial`,
`isAsymptoticScale_plMonomial_pow`, and
`isAsymptoticScale_plMonomial_log`.  Together with the three-way limit API in
`TransseriesScaleDominance.lean`, these make the chosen lexicographically
decreasing sequence consequence of `plt:lem:mot-dominance` **Exact**.  They do
not replace the source's unordered set-indexed scale by a formal set-indexed
API.

`TransseriesScaleDominance.lean` is exhaustively 1+7.  Its definition is
`plMonomial`; its theorems are `tendsto_plMonomial_atTop_zero`,
`plMonomial_div_eventuallyEq`, `tendsto_plMonomial_div_atTop_zero`,
`tendsto_plMonomial_div_atTop_one`, `plMonomial_pos`,
`tendsto_plMonomial_div_atTop`, and
`plMonomial_generators_dominance`.  Together with the preceding 0+4 leaf,
these declarations make the displayed three-way limits and every chosen
decreasing sequence scale **Exact**.  The compound
`plt:lem:mot-dominance` remains **Partial** because the unordered set-indexed
scale and a named reverse generator implication are not packaged.

`TransseriesHeight.lean` has no definitions and three theorems:
`isLittleO_log_pow_rpow`, `isLittleO_log_pow_id`, and
`isLittleO_pow_mul_log_pow_exp`.  The displayed `q0:eq:height` comparison and
its logarithm-versus-power dual are **Exact**.  The broader prose taxonomy and
comparison algorithm for arbitrarily nested exponential heights and
logarithmic depths remain **Partial**.

`TransseriesBlockAntiderivative.lean` is exhaustively 3+12.  Its definitions
are `blockOperator`, `blockAntiderivative`, and `resonantAntiderivative`.  Its
theorems are `sum_sub_sum_shift`, `blockOperator_zero`, `blockOperator_sub`,
`blockOperator_blockAntiderivative`, `blockOperator_surjective`,
`natDegree_C_mul_of_ne_zero`, `natDegree_blockOperator`,
`blockOperator_injective`, `blockOperator_bijective`,
`derivative_resonantAntiderivative`, `derivative_surjective`, and
`natDegree_resonantAntiderivative`.

`TransseriesDifferentialBlock.lean` is now exhaustively 0+12.  Its theorems are
`derivation_pow_t`, `derivation_block`, `derivation_zpow_block`,
`exists_zpow_block_primitive`, `existsUnique_zpow_block_primitive`,
`exists_block_primitive`, `derivation_block_zero`, and
`exists_block_primitive_resonant`, together with the retained wrappers
`derivation_val_inv`, `derivation_pow_inv`, `derivation_zpow_t`, and
`derivation_block_zpow`.  The three newly public Laurent theorems
give the source-shaped integer block law, nonresonant existence with preserved
logarithmic degree, and uniqueness under explicit injectivity of evaluation at
`L`.  The integer formula `plt:eq:mot-block-derivative` is **Exact**, as are
the polynomial-operator clauses.  The compound
`plt:lem:mot-block-antiderivative` remains **Partial**: the implementation uses
an abstract ambient field rather than constructing the concrete Laurent ring,
does not prove evaluation injectivity for that concrete model, and has no
single resonant uniqueness-up-to-constants wrapper.

`UnitSeriesBellCoefficients.lean` has no public definitions and exactly sixteen
theorems: `ordPartialBell_eq_factorialRatio_partialBell`,
`factorial_mul_ordPartialBell_eq_factorial_mul_partialBell`,
`coeff_fallingSeries_subst_eq_sum_ordPartialBell`,
`coeff_fallingSeries_subst_eq_sum_ordPartialBell_of_pos`,
`coeff_fallingSeries_subst_eq_sum_partialBell`,
`coeff_negBinomSeries_subst_eq_sum_ordPartialBell`,
`coeff_negBinomSeries_subst_eq_sum_ordPartialBell_of_pos`,
`coeff_logOf_eq_sum_ordPartialBell`,
`egfA_factorialDenormalize_coeff_eq`,
`bellWeightSeries_factorialDenormalize_coeff_eq`,
`coeff_logOf_eq_sum_partialBell`, `coeff_exp_subst_eq_completeBell`,
`coeff_exp_subst_eq_partitionExpSum`,
`coeff_exp_subst_eq_sum_weightedPartitions`,
`coeff_exp_subst_eq_sum_div_weightedPartitions`, and
`coeff_exp_subst_recurrence`.  The `p0:lem:bell-conversion`,
`p0:lem:power-log`, and `p0:cor:exp-log-jets` correspondence is **Exact as
formal power-series algebra**; no analytic convergence or logarithm branch is
asserted.

`QuadraticCoreCatalan.lean` is exhaustively 3+8.  Its definitions are
`quadHalf`, `halfBinom`, and `quadCoef`; its theorems are `catalan_two_step`,
`quadHalf_zero`, `quadHalf_antidiagonal`, `halfBinom_step`, `quadHalf_rat`,
`quadCoef_rat`, `quadCoef_zero`, and `quadCoef_rec`.  The Catalan coefficient
statement `p6:prop:quadratic-core-catalan` is **Exact**.  The larger
`p6:lem:quadratic-core` remains **Partial**: the named family satisfies the
quadratic equation coefficient by coefficient, but there is no packaged full
power-series identity, positive-valuation uniqueness theorem, or formal
square-root identity.  `p6:thm:deepest-pole`, identifying this algebraic family
inside the Gamma and Barnes inversions, remains unformalized.

#### Terminating `₂φ₁` reversal and q-Chu--Vandermonde tranche

In the origin progression, that public API growth left the module count
unchanged and added twelve declarations to the immediately preceding
901/11,418 inventory.
`TwoPhiOneReversal.lean` grows from 1+6 to 2+12 (one definition and six
theorems added), and `QChuVandermonde.lean` grows from 0+5 to 0+10 (five
theorems added).  The resulting origin q-Chu checkpoint was therefore exactly
901 modules and 11,430 public declarations; carrying the unique local bridge
gives 11,431.  The generating-function tranche below is the subsequent live
increment.

The exhaustive `TwoPhiOneReversal.lean` inventory is two definitions,
`twoPhiOneFinite` and `twoPhiOneReflection`, and twelve theorems:
`choose_two_add_succ_choose_two`, `finiteQPochhammerIn_sub_eq`,
`finiteQPochhammerIn_reversal_ne_zero`,
`finiteQPochhammerIn_inv_pow_self`, `twoPhiOneReflection_involutive`,
`twoPhiOneFinite_reversal`, `twoPhiOneFinite_reversal_twice`,
`twoPhiOneFinite_eq_sum_twoPhiOneTerm`,
`twoPhiOne_eq_twoPhiOneFinite_inv_pow`, `twoPhiOne_reversal`,
`twoPhiOne_reversal_twice`, and `twoPhiOne_one_eq_twoPhiOneFinite_zero`.
The monograph label `lem:2phi1-reversal` is **Exact**: the theorem is exposed
for the actual `twoPhiOne` tsum, the terminating bridge has no analytic
convergence premise, reflection is involutive, and double reversal cancels
both prefactors.  The reversal retains exactly `q,a,c,z ≠ 0` and nonvanishing
of `(q;q)_n`, `(c;q)_n`, and `(q^{1-n}/a;q)_n`; its separate `n=0` bridge
also covers `q=0`.

The exhaustive `QChuVandermonde.lean` inventory has no definitions and ten
theorems: `two_mul_choose_two`, `mul_sub_one_eq_mul_sub_add`,
`finiteQPochhammerIn_div_eq_sum_chu`, `q_chu_vandermonde_first`,
`finiteQPochhammerIn_div_eq_sum_chu_second`,
`twoPhiOneFinite_mul_finiteQPochhammerIn_eq_chu_second`,
`q_chu_vandermonde_second`, `q_chu_vandermonde_second_by_reversal`,
`twoPhiOne_q_chu_vandermonde_first`, and
`twoPhiOne_q_chu_vandermonde_second`.  The label `cor:q-chu` is **Exact**:
both formulas have actual-`twoPhiOne` wrappers throughout their displayed
rational domain `q ≠ 0`, `A ≠ 0`, `(q;q)_n ≠ 0`, `(C;q)_n ≠ 0`; in
particular the second formula assumes neither `C ≠ 0` nor `(A;q)_n ≠ 0`.
The label `prop:qchu2-by-reversal` is **Partial**.  Its provenance theorem
uses `twoPhiOneFinite_reversal` only on the additional locus `C ≠ 0` and
`(A;q)_n ≠ 0`; the stronger full-domain finite theorem and actual-tsum
wrapper instead follow from a direct denominator-cleared q-Cauchy argument.
The monograph's rational-continuation step and cleared commutative-ring
extension remain unformalized.

#### Geometric Richardson generating-function tranche

`GeometricRichardsonGenerating.lean` adds one source module and exactly ten
public declarations to the origin 901/11,430 q-Chu checkpoint, giving the
origin 902/11,440 inventory and the authoritative local 902/11,441 union after
the unique public bridge is retained.  Its three definitions
are `geometricRichardsonKernel`, `qPochhammerNormalizedDataSeries`, and
`geometricRichardsonTransform`.  Its seven theorems are
`coeff_rescale_qPochhammerSeries_eq_geometricRichardsonKernel`,
`coeff_qPochhammerNormalizedDataSeries`,
`geometricRichardsonTransform_generating`,
`geometricRichardsonTransform_eq_sum_lagrange`,
`geometricLagrangeRichardson_generating`,
`hasSum_geometricRichardsonTransform_mul_pow`, and
`hasSum_geometricLagrangeRichardson_mul_pow`.  Two private proof helpers are
excluded from the public count.

The comb-interpolation label `gq:thm:richardson-generating` is **Exact** via
`geometricLagrangeRichardson_generating`.  The stronger formal layer works
over every commutative ring, with no topology or `QRegular` hypothesis, and
uses `Ring.inverse` to make coefficients total even when a finite
q-Pochhammer factor is not a unit.  Over a field, `q ≠ 0` identifies this
convolution with the canonical totalized Lagrange row.  Roots of unity need
not be excluded for the algebraic equality, but colliding nodes are not
thereby a valid interpolation scheme; at `q = 0`, nodes repeat for `n ≥ 2`
and the closed Lagrange formula fails, so the report-facing bridge correctly
excludes that base.  The analytic pair assumes a complete normed field,
`‖q‖ < 1`, and norm-summability of the normalized data series at the chosen
`z`; the Lagrange form additionally assumes `q ≠ 0` and proves a `HasSum`
identity.  It does not claim a general analytic evaluation operation for
arbitrary formal power series.

#### Gaussian-binomial second-moment tranche

The later strengthening of the existing `GaussianBinomialCumulants.lean`
module left its then-live module count at 905 and added three public theorems,
bringing that target-side historical checkpoint to 11,474 public declarations;
with the retained public q-Pochhammer bridge the corresponding semantic-union
count is 11,475.  On the earlier source branch the same three-theorem delta left
the module count at 902 and brought the target census to 11,443 and the
bridge-retaining semantic union to 11,444.  The module's exhaustive public
inventory is two definitions, `meanAtOne` and `varAtOne`, and twenty-four
theorems: `meanAtOne_one`, `varAtOne_one`, `meanAtOne_mul`, `varAtOne_mul`,
`meanAtOne_prod`, `varAtOne_prod`, `eval_one_derivative_X_pow`,
`eval_one_derivative_derivative_X_pow`, `eval_one_qInt_X`,
`eval_one_derivative_qInt_X`, `eval_one_derivative_derivative_qInt_X`,
`meanAtOne_qInt_X`, `varAtOne_qInt_X`, `one_sub_X_pow_succ_eq`,
`gaussianBinomial_X_mul_prod_qInt`, `eval_one_gaussianBinomial_X`,
`sum_mean_diff`, `sum_var_diff`, `meanAtOne_gaussianBinomial_X`,
`varAtOne_gaussianBinomial_X`, `eval_one_derivative_gaussianBinomial_X`,
`eval_one_derivative_derivative_gaussianBinomial_X`,
`twelve_mul_secondMoment_gaussianBinomial_eval_one`, and
`twelve_mul_varianceNumerator_gaussianBinomial_eval_one`.

The last three are the new declarations.  The first gives the explicit second
derivative at one over a characteristic-zero field when `k ≤ n`.  The other
two clear all denominators: over every commutative semiring and for all natural
`n,k`, including the above-row zero case, they give the raw second coefficient
moment and the variance numerator.  The probability terminology is the
interpretation of the normalized coefficient generating polynomial; the
generic theorems themselves are algebraic identities and do not construct a
separate probability-space random variable.  Three private transport helpers
are excluded from the public census.

#### Exact Lambert branch-pairing tranche

The three-module Lambert branch-pairing union is exhaustively counted as
`LambertWBranchPairing.lean` 0+7, `LambertWGapBijection.lean` 4+16, and
`LambertWBranchSymmetry.lean` 0+9: four definitions and 32 theorems, hence 36
public declarations.  The incoming d8b delta contributes thirteen declarations
across this final surface.  The seven pairing theorems are
`principalLambertW_sub_lowerLambertW_pos`,
`lowerLambertW_eq_principalLambertW_mul_exp_gap`,
`principalLambertW_eq_neg_gap_div`,
`lowerLambertW_eq_neg_gap_mul_exp_div`,
`lowerLambertW_eq_neg_gap_div_one_sub_exp_neg`,
`eq_neg_gap_div_mul_exp`, and
`principalLambertW_lowerLambertW_eq_of_exp_gap`.

The converse module defines `gapPrincipal`, `gapLower`, `gapArg`, and
`branchGap`.  Its sixteen theorems are `gap_denominator_pos`,
`gapPrincipal_mem_Ioo`, `gapLower_eq_mul_exp`, `gapLower_eq_sub`,
`gapLower_lt_neg_one`, `gapLower_mul_exp`, `gapArg_mem_Ioo`,
`principalLambertW_gapArg`, `lowerLambertW_gapArg`, `branchGap_gapArg`,
`gapArg_branchGap`, `branchGap_invOn`, `branchGap_bijOn`,
`principalLambertW_gapArg_log`, `lowerLambertW_gapArg_log`, and `gapArg_log`.
Together with the forward formulas they prove that the positive gap and the
explicit reconstructed argument are two-sided inverses between the strict
domains `(-exp(-1),0)` and `(0,∞)`.  The final three declarations give all
three `t=exp Δ`, `t>1` forms: the principal branch, lower branch, and common
argument.

The nine symmetric theorems are
`lowerLambertW_div_principalLambertW_eq_exp_branchGap`,
`principalLambertW_add_lowerLambertW_eq_exp_branchGap`,
`principalLambertW_add_lowerLambertW_eq_cosh_div_sinh_branchGap`,
`principalLambertW_mul_lowerLambertW_eq_exp_branchGap`,
`principalLambertW_mul_lowerLambertW_eq_sinh_sq_branchGap`,
`principalLambertW_add_lowerLambertW_lt_neg_two`,
`principalLambertW_mul_lowerLambertW_pos`,
`principalLambertW_mul_lowerLambertW_lt_one`, and
`principalLambertW_mul_lowerLambertW_mem_Ioo`.  They record the exact branch
ratio, both exponential and hyperbolic sum/product forms, and the strict
interior inequalities `W₀+W₋₁<-2` and `0<W₀W₋₁<1`.  Their hypotheses exclude
both the branch point and zero endpoint.  These three finite modules do not
themselves prove a Bernoulli-number series or any branch-point or small-input
asymptotic; the separate analytic series leaf is inventoried next.

#### Exact Lambert branch-gap Bernoulli tranche

`LambertWBranchGapBernoulli.lean` first added one source module and four public
theorems to the historical 902/11,443 checkpoint, giving the historical exact-radius
checkpoint 903/11,447.  Its fifth public theorem leaves the module count fixed
and brings the target checkpoint to 903/11,448; retaining this tree's unique
public q-Pochhammer bridge gives the corresponding historical semantic-union
checkpoint 903/11,449.  Its exhaustive public surface is
`summable_norm_bernoulli_mul_pow_div_factorial`,
`summable_bernoulli_mul_pow_div_factorial_iff`,
`hasSum_bernoulli_mul_pow_div_factorial`,
`hasSum_bernoulli_mul_pow_div_factorial_complex_iff`, and
`principalLambertW_lowerLambertW_eq_bernoulliSeries`; five private majorant,
coefficient-transport, norm-transport, zeta-lower-bound, and even-term helpers
are excluded from the public count.  Together with the three finite
branch-coordinate modules, this makes the four-module Lambert union four
definitions and 37 theorems, 41 declarations.

The first theorem proves absolute convergence of the real Bernoulli
exponential generating series for `|z| < 2π`.  The second proves for every
complex `z` that the series is summable exactly when `‖z‖ < 2π`; consequently
every boundary and exterior point diverges, and its proof exhibits an
even-indexed subsequence whose term norms stay at least `2`.  The third gives the real
series its actual `HasSum` value `z/(exp z-1)` under the additional condition
`z ≠ 0`.  The fourth theorem gives the strongest complete complex statement:
the series has sum `(complexExpm1Div z)⁻¹` exactly when `‖z‖ < 2π`, including
value `1` at the removable origin.  The final theorem specializes the real
evaluation to
`x ∈ (-exp(-1),0)` and
`branchGap x < 2π`, returning both branch identities as one conjunction.  It
makes Lambert Guide label `eq:pair-Bernoulli-general` **Exact**.  Label
`eq:bernoulli-gen` is also **Exact** only when its displayed quotient is read as
the canonical removable-origin representation `(complexExpm1Div z)⁻¹`; this
does not assert equality to Lean's literal totalized quotient at `z=0` or a
holomorphy theorem.  The real quotient theorem deliberately excludes `z=0`,
while the branch theorem excludes both endpoints.  No remainder estimate or
higher/convergent Puiseux expansion is included.

#### Arbitrary-space geometric-uniform realization tranche

`GeometricUniformRealization.lean` adds one source module, one definition, and
seventeen theorems.  The definition is `geometricUniformRealization`.  The
theorems are `geometricUniformRealization_eq_tsum`,
`geometricUniformRealization_split`, `uniformProcess_hasLaw_uniformProduct`,
`weightedUniformSeries_hasLaw_of_iIndep_uniform`,
`geometricUniformRealization_hasLaw`,
`summable_norm_geometricUniformRealization_terms`,
`geometricUniformRealization_mem_Icc`,
`map_geometricUniformRealization_support_eq_Icc`,
`integral_geometricUniformRealization_eq_one_half`,
`one_sub_geometricUniformRealization_hasLaw`,
`geometricUniformRealization_identDistrib_one_sub`,
`affine_uniform_geometric_hasLaw`,
`geometricUniformRealization_identDistrib_affine`,
`measureReal_geometricUniformRealization_le_eq_cdf`,
`measureReal_geometricUniformRealization_le_eq_integral`,
`measureReal_geometricUniformRealization_le_eq_zero_of_nonpos`, and
`measureReal_geometricUniformRealization_le_eq_one_of_one_le`.

The definition, literal tsum identity, and absolute-convergence theorem are
pointwise on any type.  The probabilistic transport applies on any supplied
measurable space and measure carrying `Icc 0 1`-valued coordinates whose
marginals have the interval-volume law and which satisfy `iIndepFun`; it does
not construct those coordinates on every probability space.  Under `|q|<1`
the realization has the canonical law, mean `1/2`, reflection symmetry, and
canonical CDF.  The range, support, and exterior-CDF statements use
`0≤q<1`; the conditioning integral uses `0<q<1`.  The affine fixed-point
wrappers additionally assume `IsProbabilityMeasure P` and the displayed
independence of the fresh uniform coordinate and canonical-law copy.  Thus the
q-monograph's `thm:geometric-uniform-basic` is Exact on its stated `0<q<1`
domain, without silently asserting universal existence of a realization.

#### Regular central q-binomial-sum tranche

`RegularCentralQBinomialSum.lean` adds one source module and exactly three
public declarations: definitions `qNumberC` and
`regularCentralQBinomialTerm`, and theorem
`hasSum_regularCentralQBinomial`.  For real `0<q<1` and complex `alpha`, it
proves the actual series `HasSum` with value
`qGammaC (q^2) (3/2) * qGammaC (q^2) ((alpha+1)/2) /
qGammaC (q^2) ((alpha+2)/2)`.  Its sole parameter condition is
`qPochhammerInfIn (q^(alpha+1)) (q^2) ≠ 0`, exactly the simultaneous
nonvanishing condition for the generalized q-numbers in the summand.  Even
negative integral `alpha` are not excluded; at those parameters the totalized
q-Gamma quotient, like the product evaluation used in the proof, is zero.
This closes `thm:regular-central-sum`; it does not formalize the separate
classical-limit corollary.

#### Effective fixed-column Gaussian-rate tranche

`GaussianBinomialFixedColumnRate.lean` adds one source module, no definitions,
and exactly ten theorems:
`norm_finiteQPochhammerIn_pow_sub_one_le_exp`,
`norm_finiteQPochhammerIn_pow_sub_one_le`,
`norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le`,
`norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le`,
`norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le`,
`tendsto_gaussianBinomial_add_atTop`,
`gaussianBinomial_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_shifted_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_fixedColumn_error_isBigO`, and
`gaussianBinomial_shifted_fixedColumn_error_isBigO`.

The first two estimates hold in every normed commutative ring with normalized
multiplicative norm when `‖q‖ ≤ 1`: they bound
`‖(q^m;q)_k-1‖` by `exp(k‖q‖^m)-1` and then by
`(k exp k)‖q‖^m`.  Under `k≤n`, the third gives the denominator-free relative
bound `‖(q;q)_k[n,k]_q-1‖ ≤ (k exp k)‖q‖^(n-k+1)`, which remains meaningful at
roots of unity.  Over any normed field, `‖q‖<1` suffices for the fixed and
shifted nonasymptotic additive bounds, the shifted `Tendsto`, and all four
relative/additive `IsBigO` results at the rates `q^(n-k+1)` and `q^(n+1)`.
There is no completeness or `q≠0` hypothesis, and the displayed constant is
elementary rather than sharp.  Together with the pre-existing
`tendsto_gaussianBinomial_atTop`, the imported
`tendsto_gaussianBinomial_add_const_atTop`, and the two relative-error
theorems, this discharges every clause of `thm:fixed-column-limit`; the two
additive theorems are stronger companion estimates.  The unprimed exponential
bound is likewise now owned by `QBinomialTheoremInfinite.lean` as
`norm_finiteQPochhammerIn_pow_sub_one_le_exp_of_norm_le_one`.

Together with the prior 905/11,474 branch inventory and the three-declaration
Lambert leaf, the geometric-uniform and regular-central leaves, and this final
ten-theorem leaf, the fixed-column checkpoint was 909 modules and 11,508
public declarations.

#### Greater-than-one Gaussian asymptotics

`GaussianBinomialGreaterOneAsymptotics.lean` adds no definitions and exactly
two theorems:
`gaussianBinomial_gt_one_fixedColumn_relativeError_isBigO` and
`gaussianBinomial_gt_one_central_isEquivalent`.  For real `q` under exactly
`1 < q`, the first gives the fixed-column normalization
`(q⁻¹;q⁻¹)_k * (q^(k*(n-k)))⁻¹ * [n,k]_q - 1 =
O((q⁻¹)^(n-k+1))`; natural subtraction is total, and reciprocity is invoked
only eventually once `k ≤ n`.  The second gives the central equivalence
`[2m,m]_q ~ q^(m*m) * (q⁻¹;q⁻¹)_∞⁻¹`.  Together with the existing
`gaussianBinomial_inv`, this makes `cor:qgreaterone` **Exact**.  No
shifted-central statement or wider nome domain is claimed.

#### Rvachev--Appell Hasse and geometric-decoder tranche

`RvachevAppellHasse.lean` adds one source module, one definition,
`Fabius.Appell.polynomialTransform`, and exactly fourteen theorems:
`Fabius.Appell.polynomialTransform_apply`,
`Fabius.Appell.polynomialTransform_monomial`,
`Fabius.Appell.polynomialTransform_eq_sum_hasseDeriv_of_natDegree_lt`,
`Fabius.Appell.polynomialTransform_eq_sum_hasseDeriv`,
`Fabius.rvachevReciprocalMomentRat_odd`,
`Fabius.rvachevDeconvolutionLinearMap_eq_appellPolynomialTransform`,
`Fabius.rvachevDeconvolvedPolynomial_eq_sum_even_hasseDeriv`,
`Fabius.eval_hasseDeriv_prod_X_sub_C_eq_elementarySymmetricEval`,
`Fabius.eval_rvachevDeconvolvedPolynomial_prod_X_sub_C`,
`Fabius.eval_rvachevDeconvolvedPolynomial_qFallingPower`,
`Fabius.lagrangeBasis_eq_nodalWeight_mul_prod_X_sub_C`,
`Fabius.lagrangeRvachevDecoder_eq_nodalWeight_mul_sum`,
`Fabius.geometric_nodalWeight_eq_geometricQPochhammer`, and
`Fabius.geometric_lagrangeRvachevDecoder_eq`.

The commutative-semiring foundation is the coefficientwise linear transform
which sends each monomial to the corresponding arbitrary Appell polynomial;
the two cutoff theorems identify it with a finite Hasse-derivative sum.  The
reciprocal centered-Rvachev coefficients vanish in odd degrees, so real
Rvachev deconvolution is the finite even-Hasse sum.  Taylor's coefficient
formula and Vieta's identity turn Hasse derivatives of a root product into
complementary elementary symmetric functions, yielding the displayed
q-falling-power formula with no condition on `c` or `q`.  The field-level
Lagrange factorization, general sampled-decoder formula, geometric nodal
weight, and final real specialization then give the full Gaussian
q-Pochhammer prefactor times the same finite even-moment sum.

Those algebraic identities are total at zero and colliding nodes because the
Lagrange basis uses totalized inversion; at collisions they are not cardinal
interpolation statements.  The manuscript application retains `c>0`,
`0<q<1`, the dyadic nonzero mesh, degree, and interval hypotheses required by
the separate synthesis theorems.  In composition with
`normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp` and
the generic Lagrange--Rvachev synthesis theorem, the new formulas make both
`gq:prop:q-Appell-falling` and `gq:thm:gaussian-Appell-decoder` Exact.  The
coefficients `rvachevReciprocalMomentRat` are a formal reciprocal-moment
sequence; no convergence of an analytic reciprocal MGF is asserted.  Atom
reconstruction remains owned by the separate synthesis API, and there is no
new larger matrix right-inverse or decoder-optimality theorem.

The resulting Appell/fixed-column checkpoint was 910 modules and 11,525
public declarations, with no missing module header or declaration comment.

#### Nodes-only Lagrange--Rvachev amplitude tranche

`RvachevLagrangeNodesOnly.lean` adds one definition,
`rvachevDeconvolvedPolynomialRat`, and exactly fourteen theorems:
`map_rvachevDeconvolvedPolynomialRat`,
`rvachevDeconvolvedPolynomial_eq_sum_appell`,
`eval_rvachevDeconvolvedPolynomial_eq_sum_even_iterateDerivative`,
`rvachevDeconvolvedPolynomial_prod_X_sub_C_eq_sum_appell`,
`eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_sum_even_iterateDerivative`,
`eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_nodalWeight_mul_sum_appell`,
`lagrangeRvachevDecoder_eq_nodalWeight_mul_sum_appell`,
`map_lagrangeBasis_ratCast`,
`map_rvachevDeconvolvedPolynomialRat_lagrangeBasis`,
`lagrangeRvachevDecoder_eq_ratCast`,
`rvachevRawMomentRat_eq_centeredRvachevFullMoment`,
`momentCumulant_rvachevRawMomentRat_eq_centeredRvachevFullCumulant`,
`momentCumulant_rvachevRawMomentRat_even_eq_bernoulliMersenne`, and
`rvachevReciprocalMomentRat_eq_completeBellPolynomial_neg_centeredCumulant`.

By composition these declarations give `cor:lag-nodes-only` an
**Exact/Complete** Lean counterpart; no single wrapper theorem is claimed.
The ordinary-derivative Lagrange form assumes `Set.InjOn v s`, matching
distinct nodes, while the raw omitted-node elementary-symmetric/Appell form
uses `Lagrange.nodalWeight`.  Rational nodes produce a polynomial over `ℚ`
whose coefficientwise real cast is the real decoder polynomial.  Rational
values are consequently asserted only at rational evaluation points, notably
the lattice points `k/M`, not at arbitrary irrational real points.  The
lattice identity is total when `M=0`; actual reconstruction retains its
separate nonzero and admissible-mesh hypotheses.  The complete-Bell identity
is formal coefficient-sequence algebra, not analytic reciprocal-MGF
convergence, and odd-cumulant vanishing uses the pre-existing centered-parity
theorem.  Independently, the exact decoder and atom-coefficient synthesis
declarations in `LagrangeRvachevSynthesis` make `thm:lag-cardinal`
**Exact/Complete by assembly**.  The larger compound
`thm:lag-right-inverse`, global atom synthesis, and decoder optimality remain
unpromoted.

#### Algebraic geometric-uniform moment-polynomial tranche

`GeometricUniformMomentPolynomial.lean` adds one source module and nine public
declarations.  Concurrently, the one-definition/fourteen-theorem
`RvachevLagrangeNodesOnly.lean` and zero-definition/two-theorem
`GaussianBinomialGreaterOneAsymptotics.lean` leaves moved the 910/11,525
target checkpoint to 912/11,542; the moment-polynomial leaf brought that target
checkpoint to 913/11,551, or 913/11,552 with the retained public Pochhammer
bridge.  On the earlier branch the same leaf moved the target census from
903/11,448 to 904/11,457 and the bridge-retaining semantic union from
903/11,449 to 904/11,458; those are historical checkpoints.  Its exhaustive
1+8 surface is the definition
`geometricUniformMomentPolynomial` and the theorems
`geometricUniformMomentPolynomial_zero`,
`geometricUniformMomentPolynomial_succ`,
`geometricUniformMomentPolynomial_natDegree_le`,
`geometricUniformMomentPolynomial_eval_zero`,
`geometricUniformMomentPolynomial_one`,
`geometricUniformMomentPolynomial_two`,
`geometricUniformMomentPolynomial_three`, and
`geometricUniformMomentPolynomial_four`.  Two documented residual-product
helpers are private and therefore excluded from the public count.

The recursive family is total over `ℚ[X]`.  Its zero and successor theorems
give `P_0=1` and the residual finite q-Pochhammer recurrence; the degree theorem
gives `natDegree P_n ≤ n.choose 2`; evaluation at zero gives
`P_n(0)=1/(n+1)!`; and the four final theorems give the displayed values
`P_1` through `P_4`.  These exactly close the algebraic clauses of monograph
label `thm:qF-moment-polynomial`, including the `q=0` boundary.  At this
checkpoint the canonical label moved from None to **Partial**, because its
analytic coefficient normalization had not yet been identified with the
recursive Lean family.

#### Real-MGF normalization bridge

`GeometricUniformMomentPolynomialBridge.lean` adds one source module and one
public theorem to the immediately preceding 914/11,555 scaled-geometric
checkpoint, bringing that checkpoint to 915/11,556.  Its exhaustive 0+1 surface is
`geometricUniformMomentPolynomial_eval₂_eq_mgf_taylorCoefficient`; every helper
declaration in the module is private and excluded from the public count.

For every real `q` with `|q| < 1` and every natural index, the theorem identifies
evaluation of the recursive rational polynomial by the exact formula
`P_n(q)=((q;q)_n/(1-q)^n)·(iteratedDeriv n M_q 0/n!)`, where `M_q` is the genuine
geometric-uniform MGF.  The sharp domain includes `q=0` and negative
contractions.  This supplies the
analytic normalization in frontier label `p7:thm:Pn` throughout its real
probability-law regime.  At this historical 905/11,458 checkpoint that label
still remained **Partial**, because its leading-coefficient formula and
consequent strict odd-degree drop had not yet been formalized.

#### Inner complex-product normalization bridge

`GeometricUniformComplexMomentProduct.lean` adds one source module and three
public declarations to the historical 905/11,458 real-bridge checkpoint,
bringing that incoming branch checkpoint to 906/11,461.  Its exhaustive 1+2
surface is the
definition `geometricUniformComplexMomentProduct` and the theorems
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct` and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
Its thirteen helper declarations are private and excluded from the public
count.

For every complex `q` with `‖q‖ < 1`, including `q=0` and negative real
contractions, this leaf constructs
`A_q(z)=∏' j, complexExpm1Div ((1-q)*q^j*z)`, proves locally uniform convergence
on the whole complex plane, and identifies the recursive polynomial by
`P_n(q)=((q;q)_n/(1-q)^n)·(iteratedDeriv n A_q 0/n!)`.  For nonreal `q`, this
analytic product is not described as a probability MGF; the preceding real
0+1 theorem remains the exact probability-law MGF bridge.

The later reciprocity tranche promotes
`differentiable_geometricUniformComplexMomentProduct` to the public API.
Thus the current exhaustive surface of this module is one definition and
three theorems: `geometricUniformComplexMomentProduct`,
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct`,
`differentiable_geometricUniformComplexMomentProduct`, and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
The added theorem packages differentiability on all of `ℂ`, so the product
is now publicly known to be entire; the 906/11,461 count above remains the
historical checkpoint before that theorem was public.

#### Half-base q-binomial root-simplicity tranche

After the merged exact-closure and inner-complex union reached the historical
918/11,568 checkpoint, `HalfQBinomialRootSimplicity.lean` added one source
module and one public declaration, giving the merged-main pre-local checkpoint
919 modules and 11,569 public declarations.  Its exhaustive 0+1 surface is
`halfQBinomial_sum_rootMultiplicity_two_pow`.

For every `j < n`, the theorem proves over `ℚ` that the coefficientwise
half-base q-binomial polynomial
`∑_{k≤n} (-1)^k (1/2)^(k.choose 2) halfQBinomial n k · X^k` has root
multiplicity exactly one at `2^j`.  Together with the existing complete
rational root classification, every root in that half-base locus is simple.
No arbitrary-base, arbitrary-field, or general cyclotomic simplicity claim is
made.

#### Exterior complex reciprocal-germ normalization bridge

`GeometricUniformExteriorComplexMomentGerm.lean` adds one source module and
three public declarations to the merged-main pre-local 919/11,569 checkpoint,
bringing the merged exterior checkpoint to 920/11,572.  Its
exhaustive 1+2 surface is the definition
`geometricUniformExteriorComplexMomentGerm` and the
theorems `analyticAt_geometricUniformExteriorComplexMomentGerm` and
`geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient`.
Its twelve helper declarations are private and excluded from the public
count.

For every complex `q` with `1 < ‖q‖`, the leaf defines the manuscript's actual
reciprocal germ `M_q(z)=(A_{q⁻¹}(-z))⁻¹`, proves that it is analytic at zero,
and identifies the recursive polynomial by
`P_n(q)=((q;q)_n/(1-q)^n)·(iteratedDeriv n M_q 0/n!)`.  The definition is a
total Lean inverse, but its analytic claim is deliberately local at the
origin.  It asserts no global holomorphy across poles, pole divisor, boundary
case `‖q‖=1`, or rational-function continuation in the parameter.

The inner-disc product, exterior reciprocal germ, and both Taylor-coefficient
normalizations are therefore exact.  At this historical exterior checkpoint,
monograph label `thm:qF-moment-polynomial` was still **Partial** because no
named global `RatFunc` identified those regime-wise coefficients as one
rational parameter object.  The later RatFunc tranche below closes exactly
that assembly boundary.  Label `thm:geometric-uniform-mgf` remains
**Partial**: coefficient rationality and the `q=1` specialization are now
packaged, but no public theorem packages the product's dilation/Mahler law,
normalization, formal uniqueness, exact pole data, or
direct equality of the complex product with the real MGF or characteristic
function.  Frontier label `p7:thm:Pn` and proposition
`prop:qF-P-degree-sharp` are accounted for by the following sharp-degree
tranche.

#### Sharp geometric-uniform coefficients and exact degree

`GeometricUniformMomentPolynomialDegree.lean` adds one source module and three
public declarations to the 920/11,572 exterior checkpoint, giving the
historical sharp checkpoint 921 modules and 11,575 public declarations.  Its
exhaustive 0+3 surface is
`coeff_geometricUniformMomentPolynomial_choose_two`,
`coeff_geometricUniformMomentPolynomial_choose_two_sub_one`, and
`geometricUniformMomentPolynomial_natDegree_eq`.

For every natural `n`, the first theorem identifies the coefficient at the
triangular bound with `bernoulli' n / n!`, equivalently `(-1)^n B_n/n!` in the
manuscript convention.  For `n ≥ 2`, the second gives the coefficient one
below that bound as
`-bernoulli' n/n! + bernoulli' (n-1)/(2*(n-1)!)`.  The third proves exact
natural degree `n.choose 2` for `n=1` and even `n`, including `n=0`, and
`n.choose 2-1` for odd `n>1`.  Thus `prop:qF-P-degree-sharp` is **Exact**;
together with the algebraic recurrence and boundary tranche, the represented
frontier theorem `p7:thm:Pn` is **Exact**.  The separate real bridge keeps
`p7:eq:Pn-def` Exact on real `|q|<1`.  This
purely algebraic leaf adds no analytic continuation or root-of-unity claim.
At this historical sharp checkpoint, `thm:qF-moment-polynomial` therefore
remained **Partial**; the later global RatFunc leaf promotes it by assembly.

That algebraic source checkpoint was 913 modules and 11,551 public declarations, with
no missing module header or declaration comment.  Its then-current canonical
`thm:qF-moment-polynomial` status was **Partial** exactly as stated above.

#### Thue--Morse Gamma-tower differential tranche

`ThueMorseGammaTowerDifferential.lean` adds no definitions and exactly three
theorems: `hasDerivAt_mellin_mellinKernel_parameter`,
`hasDerivAt_thueMorseGammaLog_succ`, and
`iteratedDeriv_thueMorseGammaLog`.  For every complex Mellin exponent and
positive real damping parameter, the first differentiates under the integral
and shifts `s` to `s+1`; the other two give
`L_(r+1)'(a)=(r+1)L_r(a)` and the falling-factorial iterated law through
exactly `k ≤ r`.  With the existing Gamma-tower Mellin, integral, dyadic, and
ratio results, this makes `p2:thm:gamma-tower` **Exact** on the stated `0 < a`
domain.  These theorems concern the chosen `thueMorseGammaLog` coordinate,
not a proved branch or principal-`Complex.log` identity, and assert no
nonpositive-parameter extension.

The strengthened `GeometricResidualMoments.lean` surface has no public
definitions and exactly nine public theorems.  Its new
`sum_geometricLagrangeWeight_mul_eval_scaled_geometric` theorem works over
every field under exactly
`Set.InjOn (fun k : ℕ ↦ q ^ k) (Finset.range (p + 1))`, and reproduces
`P.eval 0` for every polynomial with `P.natDegree ≤ p` and every scale `c`,
including zero.  Together with
`sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos`, this makes
`cor:scaled-geometric-moments` **Exact** by composition and strengthens the
manuscript's `c ≠ 0` hypothesis.

The resulting bridge-stage inventory was 915 modules and 11,556 public declarations,
with no missing module header or declaration comment.

#### Finite-functional, local-corner, and central-Legendre closure tranche

The final exact-closure tranche adds two modules and nine public declarations
to the 915/11,556 bridge checkpoint.  That exact-closure checkpoint was
therefore 917 modules and 11,565 public declarations.  With the subsequent
inner complex-product union, the next historical checkpoint was 918 modules
and 11,568 public declarations.  The half-base root-simplicity leaf gave the
merged-main pre-local checkpoint 919/11,569; the exterior reciprocal-germ leaf
then gave 920/11,572; and the sharp coefficient-and-degree leaf gave the
historical 921/11,575 checkpoint.  `RvachevLaurentLeading.lean` then gave
922/11,582, `FinitePrefixAppellRecovery.lean` gave the historical pre-RatFunc
checkpoint 923/11,610, and `GeometricUniformMomentRatFunc.lean` gave the
historical RatFunc checkpoint 924/11,615.  The two new
`ProbabilityLaplaceMoments.lean` theorems gave 924/11,617, and
`RvachevLegendreBiorthogonality.lean` gave the historical facade inventory 925
modules and 11,619 public declarations, with no missing module header or public
declaration comment at that checkpoint.  Later merged work reached the
pre-reciprocity 930/11,678 checkpoint; reciprocity then gave the historical
931/11,685 checkpoint, and the dyadic-boundary and finite-prefix-collapse
leaves gave the historical 933/11,695 checkpoint.  The incoming base-two
Prouhet bridge and the strengthened dyadic-boundary and Newman APIs described
below give the historical 934/11,709 inventory.  The later transseries
checkpoints culminate in the historical 944/11,806 inventory; the sixteen-module
overlay gave the historical 960/11,966 inventory with no missing module header
or public declaration comment.  The focused-build-verified
`StirlingCompleteHomogeneous` leaf gave the historical 961/11,974 checkpoint.
The overlapping incoming route also recorded 943/11,787, 952/11,881, and
952/11,884 checkpoints, followed by 967/12,001, 969/12,048, and 970/12,051.
The reconciled 970/12,056 and preceding 977/12,133, 979/12,142, and 985/12,199 checkpoints
are historical.  The authoritative merged audit is 1004/12,500, again with no missing module header or public
declaration comment.

`FinitePolynomialFunctional.lean` remains a zero-definition module and now has
exactly sixteen public theorems:
`sum_weight_mul_eval₂_eq_sum_coeff_mul_moment`,
`sum_weight_mul_eval₂_eq_eval₂_of_moments`,
`sum_weight_mul_eval₂_eq_coeff_mul_moment`,
`sum_weight_mul_eval₂_eq_topCoeff_mul_moment`,
`sum_weight_mul_eval₂_eq_constantCoeff_mul_sum`,
`sum_weight_mul_eval₂_eq_constantCoeff`,
`sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments`,
`sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment`,
`sum_weight_mul_eval₂_eq_zero_of_degree_lt`,
`sum_weight_mul_eval₂_congr_of_map_coeff_eq`,
`sum_weight_mul_eval_eq_eval_of_moments`,
`sum_weight_mul_eval_eq_coeff_mul_of_moments`,
`sum_weight_mul_eval_eq_coeff_mul_top_moment`,
`sum_weight_mul_eval_eq_zero_of_degree_lt`,
`sum_weight_mul_eval_congr_of_coeff_eq`, and
`sum_weight_mul_eval_affine_of_topCoeff_extractor`.
The first ten are scalar-extension results from an arbitrary semiring to a
commutative semiring; the five same-ring conveniences and the affine theorem
need only a commutative semiring.  The common proof expands `eval₂` into its
finite coefficient sum, swaps the two finite sums, and inserts the prescribed
moments.  For affine transport, apply the supplied extractor to
`p.comp (C b * X + C a)` and compute its degree-`n` coefficient as
`p.coeff n * b^n`; a separate zero-scale argument retains `b=0` and `n=0`.
No distinctness, nonzero scale, subtraction, or nonzero surviving moment is
assumed.  Composing the affine theorem with
`halfQBinomial_negativeDyadic_polynomial_sum_eq_mersenne` makes
`cor:geometric-prouhet-affine` **Exact** under the existing rational-polynomial
convention.

`ThueMorseCornerIntegral.lean` has one public definition,
`centeredBoxIntegral`, and exactly four public theorems:
`centeredBoxIntegral_zero`, `centeredBoxIntegral_succ`,
`symmetricMixedDifference_range_eq_centeredBoxIntegral`, and
`symmetricMixedDifference_univ_eq_centeredBoxIntegral`.
For nonnegative half-steps, an open order-connected set `I`,
`ContDiffOn ℝ N g I`, and containment of the full symmetric segment
`[x-∑i<N,a i,x+∑i<N,a i]` in `I`, the last two theorems identify the range and
`Fin N` corner sums with the centered nested integral of `iteratedDeriv N g`.
The induction peels the final mixed difference, applies the local interval FTC
at every powerset corner, moves the finite sum through the outer integral, and
recurses on `deriv g`.  These are genuinely local hypotheses, not a global
`ContDiff` replacement.  Zero half-steps and `N=0` are included, strengthening
the printed positive-step domain; arbitrary signed half-steps are not claimed.
Together with `ThueMorseSymmetricDifference.lean`, this makes
`thm:TM-corner` **Exact**.  The following Walsh conditional-expectation
corollary remains outside the surface.

`RvachevLegendreCentralSum.lean` has no public definitions and exactly three
public theorems: `eval_legendrePolynomial_even_zero`,
`eval_rvachevLegendreDeconvolutionPolynomial_even`, and
`rvachevLegendreCentralSum`.  The last theorem assumes
`F : BoundedFabius`, `IsFabius F`, and `n : ℕ`, sets the exact mesh
`M=4^n`, and proves the printed finite central-binomial cancellation, including
`n=0`.  Its proof evaluates the existing even-mode synthesis at zero, truncates
the open block from `|k|<2M` to `|k|<M` by compact support, pairs the remaining
nonzero nodes using the two evenness facts, clears `M`, and inserts the exact
central value of `P_(2n)`.  Hence `cor:leg-central-sum` is **Exact/Complete**.
No Jacobi closed form, all-degree decoder parity or rationality, reverse
spectral closure, mesh minimality, or larger Lagrange right-inverse statement
is inferred.

#### Half-base roots, Laurent-leading, and finite-prefix Appell recovery tranche

The half-base root leaf first raised the historical 918/11,568 complex-product
checkpoint to 919/11,569.  After the exterior and sharp-degree leaves produced
920/11,572 and the historical sharp checkpoint 921/11,575, the two subsequent
upstream leaves add exactly two modules and 35 public declarations:
`RvachevLaurentLeading.lean` gives 922/11,582, and
`FinitePrefixAppellRecovery.lean` gives the historical pre-RatFunc checkpoint
923 modules and 11,610 public declarations.  The subsequent global RatFunc
leaf gives the historical 924 modules and 11,615 public declarations; the
post-RatFunc probability and finite-biorthogonality additions below gave the
historical 925 modules and 11,619 public declarations, with no missing module
header or public declaration comment at that checkpoint.  Later source work
and reciprocity gave the historical 931/11,685 checkpoint; the dyadic-boundary
and finite-prefix-collapse leaves then gave the historical 933/11,695
checkpoint.  The incoming one-module/fourteen-declaration tranche gives the
historical 934/11,709 inventory.  The later transseries tranches give the
historical 944/11,806 inventory; the sixteen-module overlay gave the historical
960/11,966 inventory with no documentation gaps.  The registered
`StirlingCompleteHomogeneous` leaf gave the historical 961/11,974 checkpoint.
The overlapping incoming route recorded 943/11,787, 952/11,881, and
952/11,884 checkpoints, followed by 967/12,001, 969/12,048, and 970/12,051.
The reconciled 970/12,056 and preceding 977/12,133, 979/12,142, and 985/12,199 checkpoints
are historical; the live inventory is 1004/12,500, with no documentation gaps.

`HalfQBinomialRootSimplicity.lean` has no public definitions and exactly one
public theorem, `halfQBinomial_sum_rootMultiplicity_two_pow`.  Over `ℚ`, for
every `j<n`, it proves root multiplicity one at `2^j` for the coefficientwise
half-base q-binomial polynomial.  The proof differentiates the finite product:
at `2^j` every product-rule term except the deleted-`j` factor vanishes, and
the remaining product is nonzero.  Together with
`halfQBinomial_sum_eq_zero_iff` and
`gaussianBinomial_half_eq_halfQBinomial`, this supplies exactly the manuscript
polynomial's roots `1,2,…,2^(n-1)`, proves that all are simple, and excludes
all other rational roots.  Thus `cor:halfbase-root-locus` is **Exact by
composition**.  No arbitrary-characteristic simplicity statement or
arbitrary-base root classification is inferred.

`RvachevLaurentLeading.lean` adds one definition,
`rvachevCenteredMGF`, and exactly six theorems:
`rvachevCenteredMGF_eq_rvachevFourierProduct`,
`rvachevCenteredMGF_pi_mul_I_int`,
`rvachevCenteredMGF_pi_mul_I_int_ne_zero_of_odd`,
`tendsto_sub_pow_mul_inv_rvachevFourierProduct_int`,
`tendsto_rvachevCenteredMGF_laurent_int`, and
`tendsto_rvachevCenteredMGF_laurent_two_pow_mul_odd`.
The definition corrects for the existing generating function's half-scale by
setting `M(t)=centeredComplexGeneratingFunction F (2*t)`; the first theorem
then proves the exact rotation `M(t)=Φ(i*t/(2π))`.  The generic limit cancels
the order `padicValNat 2 |m|+1` of every nonzero integer zero of `Φ` and tends
to the inverse analytic cofactor.  Transport through the rotation gives the
integer centered-MGF limit.  Finally, if `n=2^v*u` with `u` an odd signed
integer, the manuscript-normalized wrapper proves pole order `v+1` and
leading coefficient `-T_n^(v+1)/M(π*i*u)` at `T_n=2π*i*n`; the preceding
odd-core theorem proves the displayed denominator nonzero.  Every reciprocal
limit is taken through `𝓝[≠]`, not the full neighborhood: Lean's inverse is
totalized by `0⁻¹=0` at the pole.  This makes
`is:p2:thm:Laurent-leading` **Exact** without asserting lower Laurent
coefficients, pole-shell summation, or Appell-coefficient asymptotics.

`FinitePrefixAppellRecovery.lean` adds eleven definitions:
`unitUniformRawMomentRat`, `centeredUnitUniformRawMomentRat`,
`dyadicPrefixScaleRat`, `dyadicPrefixMomentRat`,
`uncenteredDyadicPrefixMomentRat`, `centeredDyadicPrefixMomentRat`,
`kabayaIriAppellPolynomialRat`,
`uncenteredDyadicPrefixAppellPolynomialRat`,
`centeredDyadicPrefixAppellPolynomialRat`,
`uncenteredDyadicPrefixAppellScalePolynomialRat`, and
`centeredDyadicPrefixAppellScalePolynomialRat`.  Its exactly seventeen public
theorems are `Appell.poly_binomialConv`, `Appell.binomialConv_dilate`,
`Appell.dilate_dilate`, `dyadicPrefixMomentRat_zero`,
`uncenteredDyadicPrefixMomentRat_zero`,
`centeredDyadicPrefixMomentRat_zero`,
`dyadicPrefixMomentRat_binomialConv_tail`,
`binomialConv_uncenteredDyadicPrefixMomentRat_tail`,
`binomialConv_centeredDyadicPrefixMomentRat_tail`,
`uncenteredDyadicPrefixAppellPolynomialRat_eq_sum`,
`centeredDyadicPrefixAppellPolynomialRat_eq_sum_even`,
`uncenteredDyadicPrefixAppellPolynomialRat_eq_eval_scale`,
`centeredDyadicPrefixAppellPolynomialRat_eq_eval_scale`,
`natDegree_uncenteredDyadicPrefixAppellScalePolynomialRat`,
`natDegree_centeredDyadicPrefixAppellScalePolynomialRat`,
`kabayaIriAppellPolynomialRat_eq_sum_prefix`, and
`rvachevAppellPolynomialRat_eq_sum_prefix`.

The prefix moments are constructed independently by finite binomial
convolution of scaled uniform digits.  The one-step full-moment recurrences
give exact tail factorizations, reciprocal uniqueness reverses them, and the
generic Appell transform gives the complete uncentered expansion in powers of
`2^-N` and the centered even expansion in powers of `4^-N`.  As elements of
`Polynomial (Polynomial ℚ)`, their outer degrees are exactly `n` and
`⌊n/2⌋`.  That qualifier is essential: evaluating the inner polynomial at a
fixed `x` can lower the outer degree, and in the centered odd case the top
inner coefficient vanishes at `x=0`.  The final two theorems evaluate these
scale polynomials at zero with the existing geometric Lagrange rows.  From any
starting depth `N`, they recover the full Kabaya--Iri polynomial from the
`n+1` prefixes `N,…,N+n` at base `1/2`, and the full centered
Rvachev--Appell polynomial from the `⌊n/2⌋+1` prefixes
`N,…,N+⌊n/2⌋` at base `1/4`.  These are finite exact rational identities,
not limits.  Accordingly both `is:p2:thm:finite-prefix-expansion` and
`is:p2:thm:exact-recovery` are **Exact**.  No analytic MGF convergence or
universal fixed-`x` degree statement is added.

#### Completed dyadic derivative filtration

`DyadicDerivativeFiltration.lean` has zero definitions and six theorems:
`rvachevUp_eq_zero_of_one_le_abs`,
`iteratedDeriv_rvachevUp_dyadic_eq_zero`,
`iteratedDeriv_rvachevUp_dyadic_critical`,
`dyadic_depth_eq_max_nonzero_iteratedDeriv`,
`iteratedDeriv_rvachevUp_eq_extendedFabius`, and
`iteratedDeriv_rvachevUp_dyadic_below`.  The first four give support
vanishing, above-depth vanishing, the signed critical-depth value, and exact
depth detection.  The final two are the new declarations: the first identifies
every up derivative at every `x<1` with the scaled signed global Fabius value,
and the second specializes it for `m<n` and `a<2^n` to the report's
denominator-`2^(n-m)` dyadic formula.

#### Global geometric-uniform moment RatFunc bridge

`GeometricUniformMomentRatFunc.lean` adds one source module and five public
declarations to the historical pre-RatFunc 923/11,610 checkpoint, giving the
historical RatFunc checkpoint 924 modules and 11,615 public declarations.  Its
exhaustive 1+4 surface
is the definition `geometricUniformMomentRatFunc` and the theorems
`qFactorial_mul_geometricUniformMomentRatFunc`,
`eval_geometricUniformMomentRatFunc_eq_complexMomentProduct_taylorCoefficient`,
`eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient`,
and `eval_geometricUniformMomentRatFunc_one`.  All supporting declarations are
private and excluded from the public count.

The definition packages the single rational coefficient
`a_n(X)=P_n(X)/[n]_X!` in `RatFunc ℚ`.  Its global theorem proves the safe
pole-clearing identity `[n]_X!·a_n=P_n`.  Safe evaluation of this same object
is the inner complex-product Taylor coefficient for every `‖q‖<1`, including
`q=0` and `n=0`, and the exterior reciprocal-germ Taylor coefficient for every
`1<‖q‖`.  At `q=1`, where `[n]_1!=n!`, the final theorem gives the removable
specialization `a_n(1)=P_n(1)/n!`.  Together with the algebraic, inner, and
exterior tranches, this makes canonical `thm:qF-moment-polynomial` **Exact by
assembly**.  Evaluation remains conditional on denominator nonvanishing: no
value is assigned at a genuine pole, and no exact pole divisor or pole-order
theorem, analytic continuation through `‖q‖=1`, or global holomorphy of the
exterior reciprocal is claimed.  Label `thm:geometric-uniform-mgf` remains
**Partial** under the boundary stated above.

#### Complex moment-product entireness and germ reciprocity

Merged upstream additions reached the immediate pre-reciprocity checkpoint
930 modules and 11,678 public declarations.  The reciprocity tranche promotes
one theorem in the existing complex-product module and adds the new
`GeometricUniformMomentReciprocity.lean` module with one definition and five
theorems.  It therefore adds one source module and seven public declarations
in total, giving the historical reciprocity checkpoint 931/11,685.

The current exhaustive 1+3 surface of
`GeometricUniformComplexMomentProduct.lean` is the definition
`geometricUniformComplexMomentProduct` and the theorems
`hasProdLocallyUniformly_geometricUniformComplexMomentProduct`,
`differentiable_geometricUniformComplexMomentProduct`, and
`geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient`.
The promoted differentiability theorem is global on `ℂ`, so the locally
uniform product is publicly packaged as an entire function.

The reciprocity leaf's exhaustive 1+5 surface is the definition
`geometricUniformComplexMomentGerm` and the theorems
`geometricUniformComplexMomentGerm_of_norm_lt_one`,
`geometricUniformComplexMomentGerm_of_one_lt_norm`,
`analyticAt_geometricUniformComplexMomentGerm`,
`geometricUniformComplexMomentGerm_reciprocity`, and
`geometricUniformComplexMomentGerm_moment_convolution`.  The combined function
is the inner product when `‖q‖<1`, the exterior reciprocal when `1<‖q‖`, and
is analytic at zero whenever `‖q‖≠1`.  Under exactly `q≠0` and `‖q‖≠1`,
the reciprocity theorem proves
`M_q(z) * M_{q⁻¹}(-z) = 1` locally as an `EventuallyEq` in `𝒩 0`, and
the convolution theorem proves for every order `n` the exact binomial
iterated-derivative convolution with value `if n=0 then 1 else 0`.  The germ
boundary is deliberate: the inner product can have remote zeros and Lean's
inverse is total, so no global pointwise reciprocal identity or unit-circle
continuation is asserted.  This makes canonical `thm:qF-reciprocity`
**Exact**.

#### Dyadic-boundary and finite-prefix Thue--Morse-collapse census overlay

Two subsequently merged zero-definition leaves add two source modules and ten
public theorems to the historical reciprocity checkpoint 931/11,685, giving
the historical 933/11,695 inventory.

At that checkpoint, `DyadicBoundaryIdentity.lean` had exactly two public theorems,
`prod_complexSinc_prefix_mul_rvachevFourierProduct` and
`rvachevFourierProduct_dyadic_boundary`.  The first clears the finite sinc
prefix against the rescaled Rvachev product.  The second composes that identity
with the integer-zero factorization to give the denominator-cleared
dyadic-boundary equality for every natural shell and complex displacement,
without a nonvanishing hypothesis.  A quotient formulation still requires the
denominator to be nonzero.

`FinitePrefixThueMorseCollapse.lean` has exactly eight public theorems:
`Appell.sum_thueMorseSign_mul_eval_poly`,
`sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat`,
`sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_of_lt`,
`sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_self`,
`sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat`,
`sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_succ`,
`sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_of_lt`, and
`sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_self`.  The
general Appell theorem reduces a complete signed block to its Thue--Morse
power moments; the rational prefix specializations are total at depth zero,
with lower-degree cancellation and first-surviving-response corollaries.
These are finite coefficient identities rather than analytic convergence
statements.  This overlay records the merged APIs and changes no source-result
coverage status.

#### Closed-tail moments and finite Legendre--Rvachev biorthogonality

The post-RatFunc union first adds exactly two public theorems to the existing
`ProbabilityLaplaceMoments.lean` module, taking the historical 924/11,615
RatFunc checkpoint to 924/11,617.  The exhaustive added surface is
`weightedSumDistribution_real_Ici_eq_rvachevUp_of_nonneg` and
`integral_pow_weightedSumDistribution_eq_mul_intervalIntegral_rvachevUp`,
both in `Fabius.ProbabilityRepresentation`.  For `F : BoundedFabius`,
`IsFabius F`, and real `t ≥ 0`, the first theorem identifies the closed tail
of `weightedSumDistribution` with `rvachevUp F t`; atomlessness is what passes
from the previously formalized strict tail to the closed tail, via
`weightedSumDistribution_singleton`.  For every
natural `n ≥ 1`, the second identifies the full-line expectation of `x^n`
with `n * ∫ t in (0)..1, t^(n-1) * rvachevUp F t`.  Together with the existing
global distribution and integrability results, including
`rvachevUp_eq_fabiusReal_one_sub_abs` and
`rvachevUp_eq_one_sub_fabiusReal_of_nonneg`, these make every clause of
`prop:up-tail` and `cor:up-moments` **Exact** on domains at least as strong as
printed.  These are full-line identities for the canonical law representing
the manuscript's `X`, not a new arbitrary-random-variable wrapper.  The moment
theorem does not assert the `n=0` case.

`RvachevLegendreBiorthogonality.lean` then adds one source module and exactly
one definition plus one theorem, giving the historical 925/11,619 checkpoint.  Its
exhaustive public surface is `rvachevLegendreAnalysisKernel` and
`rvachevLegendreBiorthogonality`, both in `Fabius`.  For
clarity, the former is literally the normalized kernel
`((2*m+1)/2) * integral_(-1)^1 up(x-c) P_m(x) dx`.  For
`F : BoundedFabius`, `IsFabius F`, `M : ℕ`, `M ≠ 0`, and
`l ≤ padicValNat 2 M`, the theorem proves the exact normalized
analysis/synthesis pairing over the finite open block
`Finset.Ioo (-(2*M)) (2*M)` (equivalently `|k| < 2M`): the result is
`if m = l then 1 else 0`.  Thus `thm:leg-biorthogonality` is **Exact**.
The broader `thm:leg-Lambda` remains incomplete because the kernel's support,
smoothness, parity, origin values, Fourier--Bessel formula, and dyadic
rationality are not all formalized; `cor:leg-biorthogonal-matrices` remains
incomplete because no bundled matrix projector or reverse spectral closure is
provided.

#### Merged support leaves, reciprocity, and finite-prefix Thue--Morse collapse

Relative to the historical 925/11,619 checkpoint, five merged support modules
and consolidation of existing surfaces first added five modules and fifty-nine
public declarations, reaching the immediate pre-reciprocity 930/11,678
checkpoint.  The five modules account for thirty declarations:
`QPochhammerLambertForm.lean` is 0+5,
`CentralQVandermondeInfinite.lean` is 0+4,
`ThueMorseNewmanSelfSimilarity.lean` is 1+12,
`TriangularPowerProduct.lean` is 0+2, and `MeanValueBracket.lean` is 0+6.
Respectively, these expose the complex and
real Lambert exponential forms of the infinite q-Pochhammer symbol; the
central q-Vandermonde limit and its `HasSum`/`Summable`/`tsum` forms; exact
base-four Newman amplification, geometric-ray ratios, and nonconvergence; two
commutative-monoid triangular exponent products; and two-sided mean-value and
residual-to-error brackets.  Consolidation of existing source surfaces gives
the remaining net twenty-nine declarations.  The reciprocity tranche then
added one module and seven public declarations, giving the historical
931/11,685 checkpoint.  `DyadicBoundaryIdentity.lean` 0+2 and the finite-prefix
collapse leaf below added two modules and ten declarations, giving the
historical 933/11,695 checkpoint.
This census accounting records the merged public API and by itself assigns no
new frontier status to those support results.

`FinitePrefixThueMorseCollapse.lean` accounts for eight of those ten final
declarations.  It has no public definitions and exactly eight
public theorems.  The generic theorem
`Appell.sum_thueMorseSign_mul_eval_poly` states, for an arbitrary rational
Appell sequence, that the signed block on the grid `x+k*h` is the coefficient
sum with factors `(n.choose r) * h^r * thueMorsePowerSum N r` and lower Appell
polynomial `n-r`.

The uncentered main theorem
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat`
uses `thueMorseSign k` on the exact grid `x+k/2^N` and returns
`(-1)^N * 2^{-((N+1).choose 2)} * n.descFactorial N * x^(n-N)`.
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_of_lt`
specializes this to zero for `n<N`, while
`Fabius.sum_thueMorseSign_mul_uncenteredDyadicPrefixAppellPolynomialRat_self`
gives the first response
`(-1)^N * N! * 2^{-((N+1).choose 2)}`.

The centered main theorem
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat`
uses the total grid `x+(1-2^-N)-2k/2^N` and returns the sign-free response
`2^{-(N.choose 2)} * n.descFactorial N * x^(n-N)`.
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_succ`
rewrites the positive depth as `N=m+1` and uses the manuscript's literal grid
`x+(1-2^{-(m+1)})-k/2^m` with the same scale.
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_of_lt`
gives zero for `n<N`, and
`Fabius.sum_thueMorseSign_mul_centeredDyadicPrefixAppellPolynomialRat_self`
gives `N! * 2^{-(N.choose 2)}`.  The two primary theorems and both first-response
corollaries include `N=0`; only the literal-grid successor wrapper is
positive-depth-indexed.

Consequently the uncentered main theorem supplies the exact compositional
closure of `is:p2:thm:TM-uncentered`; its `_of_lt` and `_self` corollaries give
the exact Prouhet cancellation and first surviving value required by
`is:p2:cor:Prouhet-canonical`; and the centered `_succ` theorem supplies the
exact printed grid for `is:p2:thm:TM-centered`, strengthened at `N=0` by the
total centered theorem.  This is rational coefficient-model algebra only.  It
introduces no random variable or `HasLaw` theorem and proves no analytic MGF or
Barnes-function identification.

#### Base-two Prouhet, printed dyadic boundary, and Newman oscillation overlay

The incoming tranche adds one module and fourteen public declarations to the
historical 933/11,695 checkpoint, giving the historical 934/11,709
pre-transseries inventory.  The
delta is the union of the new zero-definition/six-theorem
`ProuhetBaseTwoBridge.lean` leaf, one theorem added to
`DyadicBoundaryIdentity.lean`, and seven theorems added to
`ThueMorseNewmanSelfSimilarity.lean`; it is not fourteen declarations in the
new module alone.

The live exact-name-deduplicated union is 1004 modules and 12,500 public
declarations, with no documentation gaps.

The exhaustive `ProuhetBaseTwoBridge.lean` surface is
`thueMorseSign_cast_eq_neg_one_pow_digits_sum`,
`digitPowerSum_neg_one_two`, `sum_range_two_neg_one_pow`,
`digitPowerSum_neg_one_two_eq_zero_of_lt`,
`digitPowerSum_neg_one_two_self`, and
`sub_one_pow_mul_thueMorsePowerSumRing_self`.  Over every commutative ring it
identifies the base-two digit-weighted sum at `ζ=-1` with the Thue--Morse power
sum, obtains strict-low-degree Prouhet cancellation from the general digit
machine, and gives both the closed sharp moment
`(-1)^m * 2^(m.choose 2) * m!` and its division-free general-machine form.

`DyadicBoundaryIdentity.lean` is now 0+3.  Its added theorem,
`norm_rvachevFourierProduct_dyadic_boundary`, states the printed norm-quotient
identity on exactly `0 < z < 2^k`; central-lobe positivity proves that the
divided product is nonzero.  The existing prefix-product and denominator-free
entire identities remain unchanged.

`ThueMorseNewmanSelfSimilarity.lean` is now 1+19.  Its seven added theorems are
`eight_rpow_logb_four_three`,
`sqrt_three_div_three_lt_two_div_three`, `newman_ratio_eight`,
`newman_ratio_eight_lt_two_div_three`,
`frequently_newmanRatio_eq_two_div_three`,
`frequently_newmanRatio_eq_sqrt_three_div_three`, and
`newmanRatio_oscillates`.  They identify the second recurrent ratio as
`sqrt 3 / 3`, compare it strictly with `2/3`, prove both values recur
frequently at `atTop`, and package the resulting explicit oscillation.  This
overlay preserves the incoming API descriptions and makes no additional
source-result status move.  The 934/11,709 count in this historical overlay is
the pre-transseries checkpoint; the current semantic-union census is computed
by `scripts/doc_audit.py` and pinned in `docs/doc_audit_baseline.json`.

The one-definition/eight-theorem
`RvachevSuperconvergentSynthesis.lean` leaf contributes
`IsRvachevSuperconvergentPhase`,
`isRvachevSuperconvergentPhase_two_pow_iff`,
`tsum_quarter_monomial_eq_integral_of_even_deg`,
`tsum_three_quarters_monomial_eq_integral_of_even_deg`,
`tsum_shifted_monomial_eq_integral_superconvergent`,
`tsum_shifted_polynomial_eq_integral_superconvergent`,
`integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent`,
`normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp_superconvergent`,
and
`normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent`.
It proves the stronger arbitrary-nonzero-`M` degree-`v₂(M)+1` result at the
selected exact phase representatives; it does not classify phases modulo
integers or prove maximality, positivity, or rationality.  The prime-power and
outer-product tranches
account for one module and six declarations: the zero-definition/three-theorem
`GeometricPochhammerNormalConvergence.lean` leaf and three additional theorems
in `PrimePowerBinomialValuation.lean`.  The q-polish adds two theorems to
`QPochhammerInfinite.lean`, the three-module effective-inverse union
contributes seventeen declarations, the first six q-calculus modules contribute
36 declarations, and four later leaves originally contributed 38 declarations
and now expose 40 after the two Gaussian additions.
Those leaves are `GaussianBinomialPalindromic.lean` 0+14,
`JacksonIntegral.lean` 1+7, `QExponential.lean` 3+8, and
`ThetaQuasiPeriodicity.lean` 1+6: five definitions and thirty-five theorems.
Four still newer q-series leaves contribute twenty theorems and no definitions:
`GaussianBinomialPolynomialStructure.lean` 0+5, `JacobiCubic.lean` 0+2,
`QPochhammerLogDerivative.lean` 0+10, and
`QPochhammerOrderDerivative.lean` 0+3.
The two newest algebra leaves add thirteen theorems and no definitions:
`CentralQBinomialReduction.lean` 0+6 and
`CyclotomicFactorization.lean` 0+7.
The two added Gaussian linear-coefficient theorems and the eight-declaration
`EffectiveGapInverse.lean` leaf account for ten declarations and
one module.
The finite-q tranche adds four modules and 25 declarations:
`PrimitiveRootBlock.lean` 0+3, `QLucas.lean` 0+7,
`CyclotomicDivisibility.lean` 0+3, and `QCatalan.lean` 1+11.  They add the carry criterion,
primitive-root block formula, q-Lucas theorem, and integral q-Catalan API.
The interpolation/q-beta pair now contributes four definitions and twenty-seven theorems:
`QBetaIntegral.lean` 1+8 and `NewtonInterpolation.lean` 3+19.  The former
evaluates the Jackson q-beta integral as both an infinite-product quotient and
a q-gamma quotient, with positivity, symmetry, and successor recurrences; the
latter supplies triangular Newton coefficients and the node-qualified polynomial,
interpolation and uniqueness, divided differences, the geometric-grid specialization,
and seven compatibility declarations for the `newtonInterpolant` family.
The integer/complex-upper and q-Pfaff--Saalschuetz modules contribute two definitions and eighteen theorems:
`GaussianBinomialInteger.lean` 1+10,
`GaussianBinomialComplexOrder.lean` 1+5, and
`QPfaffSaalschutz.lean` 0+3.  They extend Gaussian coefficients to integer
and principal-branch complex upper parameters, derive the associated finite
and reciprocal q-binomial series, and prove the terminating balanced
q-Pfaff--Saalschuetz summation over a field.  Their nonzero-nome,
strict-contraction, and finite-product nonvanishing hypotheses remain explicit.
`QuantumMultinomial.lean` has no definitions and exactly five
theorems.  It decomposes natural tuple antidiagonals, transports Gaussian
symmetry to arbitrary semirings, proves q-multinomial coefficient commutation,
and establishes the ordered noncommutative q-multinomial expansion from the
displayed pairwise q-commutation laws.  The API is finite and division-free.
`GaussianBinomialBounds.lean` has no definitions and exactly
six theorems: `gaussianBinomial_inv`, `one_le_gaussianBinomial`,
`finiteQPochhammerIn_pow_le_one`,
`gaussianBinomial_le_inv_qPochhammerInfIn`,
`pow_le_gaussianBinomial_of_one_lt`, and
`gaussianBinomial_le_pow_div_of_one_lt`.  They give evaluated field
reciprocity, the nonnegative strict-contraction bounds, and the resulting
dimension-dominant real bounds for `Q > 1`, with `k ≤ n` and all nonzero and
order hypotheses explicit.  The module reuses the stronger ordered-field
`finiteQPochhammerIn_self_pos` theorem from `GeneralQConditionNumber.lean`
rather than exporting a duplicate.
The rigorous forward q-monograph ledger is 181 Exact, 79 Partial, 14 None,
and 8 interface rows; its source concordance is 103 Lean, 375 human, 60 N/A,
and 9 conjecture rows, and the concordance extractor passes.
`prop:gaussian-bound` is Exact.  `thm:q-lucas` remains
Partial because the proved evaluated primitive-root identity is weaker than
the manuscript's polynomial congruence modulo `Φ_d`, and
`cor:babbage-derivative` remains Partial because only its value is formalized.
The older 622/8,472, 623/8,476, 629/8,546, 630/8,552,
641/8,650, and 643/8,661 values below are historical checkpoints, not
descriptions of the live tree.  The earlier additions and q-series tranches are
itemized below.  The branch-point geometry and
asymptotics leaves contribute 17 declarations for the one-sided vertical
tangents and leading signed square-root laws of both real Lambert branches.
The two Legendre--Gaunt modules contribute 25: four definitions and twelve
theorems in `LegendreGaunt.lean`, and one definition and eight theorems in
`FabiusLegendreGaunt.lean`.  They add the executable rational triple-product
and finite product-linearization core, then specialize it to full and even
Rvachev coefficient sums for rational and real Legendre Gram entries.  The
remaining twenty declarations are three generalized spectral q-Pochhammer
APIs, four density-diagnostic theorems, the locally uniform real-frequency
phase-prefix theorem and its compact-set uniform corollary in
`GeometricSincCharacteristicFunction.lean`, and eleven inverse-modulus
strictness and equality refinements.  `GeometricUniformMultisection.lean`
contributes two coordinate definitions and three fixed half/quarter
multisection theorems.  `GaussianBinomialAtNegOneDerivative.lean` supplies four
declarations: two first-derivative formulas at `q = -1` and two simple-root
multiplicity theorems.  Three signed-power moment theorems in
`RvachevDerivativeDistribution.lean` give the exact Boolean-cube formula and
its even-moment and positive-order odd-moment corollaries.  The same module's
two additional positive-order signed-distribution theorems give the sharply
normalized half-mixture law under exactly `0<n`:
`intervalIntegral_comp_normalized_iteratedDeriv_rvachev` is the continuous-test
half-mixture into any real Banach space, and
`map_normalized_iteratedDeriv_rvachev_restrict_Icc` is the corresponding Borel
pushforward identity for Lebesgue measure restricted to the closed interval
`[-1,1]`.  Order zero instead has the unsymmetrized original `rvachevUp` law.
The remaining declaration is the all-depth
`generalizedRvachevProduct_two_pow_mul` shift--refinement theorem in
`WeightLinearityProducts.lean`.  The final nine declarations are the two
definitions and seven theorems of `LagrangeRvachevSynthesis.lean`: the generic
finite-node decoder and atom coefficient, degree bounds, cardinal synthesis,
componentwise biorthogonality, linear coefficient identity, exact finite
interpolation loop, and unit row mass.  This inventory claim does not extend to
a geometric Gaussian closed-form decoder, a matrix wrapper, or an
optimal/minimum-variation decoder theorem.

The subsequent `LagrangeRvachevMatrix.lean` leaf is exhaustively 4+6.  Its
definitions and abbreviation are `rvachevAtomIndexSet`, `RvachevAtomIndex`,
`lagrangeRvachevEncoderMatrix`, and `lagrangeRvachevDecoderMatrix`; its
theorems are `lagrangeRvachevEncoderMatrix_nonneg`,
`sum_lagrangeRvachevEncoderMatrix_row_eq_one`,
`sum_lagrangeRvachevDecoderMatrix_row_eq_one`,
`lagrangeRvachevEncoderMatrix_mul_decoderMatrix`,
`exists_neg_entry_of_rightInverse_of_row_overlap`, and
`exists_lagrangeRvachevDecoderMatrix_entry_neg_of_row_overlap`.  It packages
the exact lattice block `Ioo (-(2*M)) (2*M)`, the normalized nonnegative
encoder and row-unital decoder, and the right-inverse equation under exactly
distinct in-range nodes, `M ≠ 0`, and `s.card - 1 ≤ padicValNat 2 M`.  The
generic sign theorem needs only encoder nonnegativity, decoder row unitality,
the right-inverse equation, and one strictly positive column in two distinct
rows; its Rvachev specialization remains conditional on that overlap.  It
asserts no `decoder * encoder` projector range/kernel, rank, trace,
characteristic-polynomial, Cauchy--Binet, geometric closed-form, or decoder
optimality result.

Two further declarations close the barycenter layer:
`ProbabilityRepresentation.integral_id_weightedUniformDistribution` gives
`(1 / 2) • ∑' n, w n` for norm-summable weights in every complete Borel real
normed space without sign, order, or termwise-integration hypotheses, and
`ProbabilityRepresentation.integral_id_geometricUniformDistribution_eq_one_half`
specializes it to mean `1 / 2` under exactly `|q| < 1`, including `q = 0` and
negative `q`.  Accordingly `GeometricUniformLaw.lean` now has 24 public
declarations.  The subsequent
`integral_polynomial_mul_rvachevUp_eq_dyadic_tsum` theorem in
`PolynomialCombExactness.lean` packages the polynomial-times-Rvachev integral
as the corresponding dyadic shifted-polynomial sum and contributes one further
declaration.  The subsequent centered Appell/deconvolution and arbitrary-phase
polynomial-reproduction tranche contributes four declarations: three in
`RvachevMomentAppell.lean` and one in `RvachevPolynomialSynthesis.lean`.
The new `QPochhammerEntire.lean` leaf retains five compatibility theorems:
locally uniform convergence of the defining products for every strict complex
contraction, complex differentiability in the free parameter, the exact
factor-zero classification (including the `q = 0` boundary), its reciprocal-
power spelling for a nonzero nome, and simple zeros expressed as analytic order
one.  Together with the branch-only four-theorem
Gaussian `q = -1` first-jet leaf, both q-series modules remain facade-reachable.
The two subsequent general q-Pochhammer modules contribute thirty-two further
declarations.  `QPochhammerDissection.lean` adds two finite residue-class
dissection theorems over an arbitrary commutative ring: the exact-multiple form
is total in `r`, and the remainder form assumes exactly `u <= r`.
`QPochhammerInfinite.lean` adds the general infinite symbol and twenty-nine
theorems covering summability and convergence for a strict norm contraction,
finite-prefix and residue-class factorizations, exact factor-zero criteria,
locally uniform parameter convergence and continuity, complex entirety,
explicit derivatives at factor zeros, derivative nonvanishing at every raw
factor zero, analytic order one at every zero, and nonvanishing of the
displayed derivative coefficient at every inverse-power zero for a nonzero nome.  Its
algebraic cofactor
identity needs only a field and a nonzero nome; its infinite dissection assumes
exactly `0 < r`, `[NormedCommRing R] [NormOneClass R] [CompleteSpace R]`, and
the strict contraction.  These are regularity statements in the free parameter
`a`, not a joint analyticity or continuation theorem in the nome `q`.

The subsequent `GeneralizedRvachevIdentifiability.lean` leaf contributes no
definitions and exactly six theorems:
`weightSequence_eq_of_weightedScaleMultiplicity_base_pow_eq`,
`analyticOrderAt_generalizedRvachevProduct_two_pow`,
`exponent_zero_eq_toNat_analyticOrderAt_generalizedRvachevProduct`,
`exponent_succ_eq_toNat_analyticOrderAt_generalizedRvachevProduct`,
`exponentSequence_eq_of_analyticOrderAt_two_pow_eq`, and
`generalizedRvachevProduct_eq_iff`.  They recover an exponent sequence from
weighted multiplicities at base powers or, under the exact summability
hypotheses, from analytic orders at `1, 2, 4, ...`, and make equality of two
admissible entire products equivalent to equality of their exponent
sequences.  The input is the multiplicity/order divisor: a bare zero set or
the product values at its zero points does not distinguish, for example, a
sequence from its double.  Spectral-zeta, cumulant-sample, and generalized
probability-law identifiability are not included.
The merged q-series leaves are inventoried below from the live source tree;
those counts supersede the intermediate pre-union q-series subtotal.
The valuation tranche's new leaf
`PrimePowerBinomialValuation.lean` contributes no definitions and exactly six
theorems.  `primePowerChoose_padicValNat_add` and
`primePowerChoose_padicValNat` are the additive and subtraction forms for row
`p^m`, including the positive right endpoint and `m=0`.
`primePowerSubOneChoose_padicValNat` says every column `j<p^m` in row
`p^m-1` is a `p`-adic unit, while
`primePowerSubTwoChoose_padicValNat` proves
`v_p(C(p^m-2,j-1))=v_p(j)` for exactly `0<j<p^m`.
`twoPowChoose_padicValNat` and `twoPowSubTwoChoose_padicValNat` are the two
strict-interior dyadic-comb wrappers.  The upper companion boundary is
necessarily excluded because at `j=p^m` the binomial coefficient is zero.
The compatibility leaf, `QPochhammerEntire.lean`, contributes no definitions
and retains exactly five theorems:
`hasProdLocallyUniformly_complexQPochhammerInf`,
`complexQPochhammerInf_differentiable`,
`complexQPochhammerInf_eq_zero_iff`,
`complexQPochhammerInf_eq_zero_iff_eq_inv_pow`, and
`analyticOrderAt_complexQPochhammerInf_of_eq_zero`.  For each fixed complex
strict contraction `q`, they give locally uniform convergence on the whole
complex `a`-plane, entireness in `a`, the raw factor-zero locus (including
`q = 0`), its reciprocal-power spelling under `q ≠ 0`, and analytic order one
at every zero.  They assert neither joint holomorphy in `q` nor a global
growth/order/type claim.  Outer spectral-product local uniformity belongs to
the separate three-theorem module recorded below.
`GeometricPochhammerNormalConvergence.lean` contributes no definitions and
exactly three theorems:
`hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`,
`hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`, and
`hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf`.  For every
complex `q` satisfying exactly `‖q‖<1`, including `q=0`, the first gives the
locally uniform outer product on the whole complex `z`-plane with limit
`geometricSincProduct q`; the other two are the nome-`1/4` Rvachev-product and
bounded-Fabius specializations.  This promotes only the locally-uniform/normal-
convergence clause.  The compound `qF` spectral theorem remains partial:
centered characteristic-function/MGF packaging, the outside-disk reciprocal
formula, the pole divisor, and the zero--pole exchange remain absent.
The two subsequent q-Pochhammer leaves contribute thirty-two declarations.
`QPochhammerDissection.lean` has no definitions and exactly two theorems,
`finiteQPochhammerIn_dissection` and
`finiteQPochhammerIn_dissection_remainder`; both are finite identities over
every commutative ring, with the remainder theorem assuming exactly `u ≤ r`.
`QPochhammerInfinite.lean` has one definition, `qPochhammerInfIn`, and exactly
twenty-nine theorems:
`qPochhammerInfIn_eq_tprod`, `summable_norm_mul_pow`,
`one_sub_ne_zero_of_norm_lt_one`, `norm_mul_pow_self_lt_one`,
`finiteQPochhammerIn_self_ne_zero`,
`multipliable_one_sub_mul_pow_of_norm_lt_one`,
`hasProd_qPochhammerInfIn`,
`tendsto_finiteQPochhammerIn_qPochhammerInfIn`,
`qPochhammerInfIn_eq_finite_mul_shift`, `qPochhammerInfIn_succ_shift`,
`qPochhammerInfIn_eq_factor_mul`, `qPochhammerInfIn_dissection`,
`qPochhammerInfIn_ne_zero`, `qPochhammerInfIn_eq_zero_iff`,
`qPochhammerInfIn_self_ne_zero`, `qPochhammerInfIn_eq_tprod_smul`,
`summable_norm_pow_of_norm_lt_one`, `isBigO_one_sub_sub_one`,
`differentiable_finiteQPochhammerIn`,
`qPochhammerInfIn_eq_zero_iff_exists_inv_pow`,
`hasProdLocallyUniformly_qPochhammerInfIn`,
`continuous_qPochhammerInfIn`,
`pow_sq_mul_finiteQPochhammerIn_inv_pow_self`,
`differentiable_qPochhammerInfIn`,
`hasDerivAt_qPochhammerInfIn_of_mul_pow_eq_one`,
`hasDerivAt_qPochhammerInfIn_inv_pow`,
`deriv_qPochhammerInfIn_inv_pow_ne_zero`,
`deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one`, and
`analyticOrderAt_qPochhammerInfIn_of_eq_zero`.  These stratify the total
topological-ring definition, strict-contraction complete-normed-ring
product/shift/dissection and multiplicative-norm zero API, complete-field
inverse-power zeros, locally compact field local uniformity and continuity,
and complex entire, nonzero-derivative, and analytic-order-one formulas,
including the raw-factor statements at `q=0`.  They make no joint-nome
holomorphy or global asymptotic claim; the separate five-theorem
`QPochhammerEntire.lean` API retains the compatibility names for
`complexQPochhammerInf`, adds the nonzero-nome reciprocal-power spelling, and
includes analytic order one at `q=0`; no public equality bridge between the
two product definitions is counted.
The final incoming seven-module increment consists of the four-theorem
`GaussianBinomialAtNegOneDerivative.lean` leaf described above and six further
q-series modules contributing exactly sixty-nine declarations.
`QBinomialTheoremInfinite.lean` contributes one definition and twenty-two
theorems: real comparison products and Gaussian majorants, fixed-column
convergence, Tannery transfer, Euler's product and reciprocal expansions, and
the infinite q-binomial theorem over complete normed fields under the stated
strict nome and series-variable contractions.  The reused theorem
`finiteQPochhammerIn_zero_left` remains canonically owned by
`GaussianBinomialAtOne.lean` and is not counted in this module.
`JacobiTripleProduct.lean`
contributes two definitions and twenty-five theorems: the exact finite
polynomial identity over commutative rings, its Laurent field form, the
complete-normed-field Jacobi sums for nonzero Laurent variable and strict
nome, and Euler's pentagonal specialization.  `QPascalSummation.lean` adds
four theorems for the two finite q-Pascal row splittings and Gaussian
coefficient commutation; `GaussianBinomialContinuity.lean` adds three for
topological-semiring continuity, the limit at one, and the field quotient
form with its nonzero denominator; and `QuantumBinomial.lean` adds the two
noncommutative-semiring quantum-plane identities under exactly the displayed
commutation hypotheses.  Finally, `RogersSzegoPolynomial.lean` contributes
one definition and nine theorems: finite commutative-(semi)ring boundary and
recurrence laws, plus the complete-normed-field generating series under
`‖q‖ < 1`, `‖t‖ < 1`, and `‖z*t‖ < 1`.  These six module counts sum to
69, and with the four q=-1 derivative declarations give the deduplicated
73-name incoming increment.  The two subsequent
`QPochhammerInfinite.lean` theorems brought that historical feature snapshot
from 622/8,472 to 629/8,547, a seven-module/75-declaration change.  The two
inverse-computability modules then brought that feature snapshot to 631/8,556,
a nine-module/84-declaration change.  The six further incoming q-calculus
leaves contribute 36 declarations and brought the intermediate audit to
649/8,697.  The four subsequent leaves contribute 38 declarations and bring
that audit to 653/8,735.  The next four leaves contribute twenty declarations
and bring that audit to 657/8,755.  The final two algebra leaves contribute
thirteen declarations and brought the audit to 659/8,768.  Two Gaussian
linear-coefficient theorems then brought it to 659/8,770, and the
eight-declaration `EffectiveGapInverse.lean` leaf brought the audit to
660/8,778.  The superconvergent synthesis leaf adds one module and nine
declarations, yielding 661/8,787.  The four root-of-unity/q-Catalan modules
add twenty-six declarations, yielding 665/8,813.  The original Jackson
q-beta/Newton pair adds twenty-four declarations, yielding 667/8,837; the
integer/complex upper Gaussian and q-Pfaff--Saalschuetz leaves add twenty,
yielding 670/8,857; and the noncommutative q-multinomial leaf adds five,
yielding 671/8,862.  `GaussianBinomialBounds.lean` adds six theorems,
yielding 672/8,868, and the seven collision-free Newton compatibility names
yield the intermediate 672/8,875 census.  The 5+14
`BinaryWordInversions.lean`, 2+8 `BoxPartitions.lean`, and 0+5
`TelescopingCertificate.lean` leaves then add three modules and thirty-four
declarations, yielding the historical 675/8,909 checkpoint.

`GaussianBinomialPalindromic.lean` is an exhaustive zero-definition,
fourteen-theorem leaf: `Fabius.reflect_add_of_natDegree_le`,
`Fabius.reflect_one'`, `Fabius.gaussianBinomial_natDegree_le`,
`Fabius.gaussianBinomial_zero_left`, `Fabius.gaussianBinomial_diag'`,
`Fabius.reflect_gaussianBinomial`,
`Fabius.coeff_gaussianBinomial_reflect`,
`Fabius.coeff_gaussianBinomial_zero`,
`Fabius.coeff_gaussianBinomial_top`, `Fabius.gaussianBinomial_natDegree`,
`Fabius.gaussianBinomial_monic`,
`Fabius.two_mul_derivative_gaussianBinomial_eval_one`,
`Fabius.coeff_gaussianBinomial_one_of_pos_of_lt`, and
`Fabius.coeff_gaussianBinomial_one`.  Over every
commutative semiring it supplies generic reflection helpers, the Gaussian
degree bound, zero and diagonal values, exact reflection in degree `k*(n-k)`,
constant and top coefficients one, bounded-index coefficient symmetry, and
the division-free derivative-at-one mean identity.  The interior linear
coefficient is one under exactly `0 < k` and `k < n`; the total classifier is
`if 0 < k ∧ k < n then 1 else 0`, so the boundary cases `k = 0`, `k = n`,
and `n < k` are explicit.  Both coefficient theorems hold over every
commutative semiring; exact degree and monicity alone require nontriviality.

An earlier retained six-module increment is exhaustively counted as
`QPochhammerInfiniteBounds.lean` 0+5, `HeineTransformation.lean` 2+5,
`QGaussSummation.lean` 0+2, `QPochhammerComplexOrder.lean` 1+4,
`BasicHypergeometricSeries.lean` 2+5, and `QMultinomial.lean` 1+9: six
definitions and thirty theorems.  It adds finite-prefix bounds, the Heine and
q-Gauss identities, a ratio-defined complex-order q-Pochhammer API, general
basic-hypergeometric terms and summability, and the division-free recursive
q-multinomial interface.  In that interface, `qMultinomial`,
`qMultinomial_nil`, and `qMultinomial_cons` need only `Semiring`; the
diagonal, singleton, pair, naturality, and universal laws use `CommSemiring`,
the factorial law uses `CommRing`, and the field quotient assumes exactly
`(q;q)_(sum l) ≠ 0`.  The displayed contraction, nonvanishing, and other
denominator hypotheses remain part of these APIs.
The four-module increment is now exhaustively counted as
`GaussianBinomialPalindromic.lean` 0+14, `JacksonIntegral.lean` 1+7,
`QExponential.lean` 3+8, and `ThetaQuasiPeriodicity.lean` 1+6.  It adds the
degree, monicity, coefficient-reversal, division-free mean theory, and total
linear-coefficient classifier of the
Gaussian polynomial; q-exponentials and their q-derivative laws; Jackson's
fundamental theorem and integration by parts; and the bilateral theta product,
quasi-periodicity, and zero criterion.  Their analytic declarations keep the
displayed strict-contraction, nonzero-variable, convergence, and nonvanishing
hypotheses.

The still newer four-module increment is exhaustively counted as
`GaussianBinomialPolynomialStructure.lean` 0+5, `JacobiCubic.lean` 0+2,
`QPochhammerLogDerivative.lean` 0+10, and
`QPochhammerOrderDerivative.lean` 0+3.  Its twenty theorems add universal
Gaussian polynomial structure over `ℕ[X]`, Jacobi's cubic identity, the
q-Pochhammer logarithmic derivative and Lambert-series form on the unit disc,
and the derivative with respect to complex order.  The strict-contraction,
unit-disc, nonzero-nome, and shifted-argument hypotheses remain explicit.

The following two-module increment is exhaustively counted as
`CentralQBinomialReduction.lean` 0+6 and
`CyclotomicFactorization.lean` 0+7.  It adds finite q-Pochhammer sign pairing,
even--odd dissection and ring-hom naturality; the division-free central
Gaussian reduction and its conditional quotient form; and the cyclotomic
factorizations of `(X;X)_n` and `[n,k]_X`.  The quotient theorem retains both
nonzero-denominator hypotheses, and the Gaussian cyclotomic factorization
retains its integral-domain assumption.

The source-only q-algebra increment adds `CentralQBinomialReduction.lean`
0+6: `finiteQPochhammerIn_mul_neg`, `finiteQPochhammerIn_two_mul`,
`finiteQPochhammerIn_map_ringHom`, `central_gaussianBinomial_sq_mul_int`,
`central_gaussianBinomial_sq_mul`, and `central_gaussianBinomial_sq_div`;
and `CyclotomicFactorization.lean` 0+7: `div_add_div_le_div`,
`div_le_div_add_div_add_one`, `mem_range_and_mem_divisors_iff`,
`finiteQPochhammerIn_X_eq_prod_cyclotomic`,
`finiteQPochhammerIn_X_eq_gaussianBinomial_mul`,
`prod_cyclotomic_pow_div_extend`, and
`gaussianBinomial_X_eq_prod_cyclotomic`.  The first module gives the
division-free central squared-base reduction over commutative rings and a
field quotient under two nonvanishing hypotheses.  The second gives the
finite-product cyclotomic factorization over commutative rings and the final
Gaussian factorization over an integral domain.

The latest finite-q tranche is exhaustive.  `PrimitiveRootBlock.lean` is
0+3: `Fabius.gaussianBinomial_isPrimitiveRoot_eq_zero`,
`Fabius.neg_one_pow_mul_pow_choose_two`, and
`Fabius.finiteQPochhammerIn_isPrimitiveRoot`.  In a commutative integral
domain, a primitive `d`-th root `ζ` kills `[d,k]_ζ` for `0 < k < d`; for
`0 < d`, the top phase is `(-1)^d * ζ^(choose d 2) = -1` and the complete
block is `(y;ζ)_d = 1-y^d`.

`QLucas.lean` is 0+7: `Fabius.add_mul_add_sub_one`, `Fabius.choose_two_add`,
`Fabius.coeff_finiteQPochhammerIn_neg_X`,
`Fabius.finiteQPochhammerIn_neg_X_block`, `Fabius.coeff_block_pow_mul`,
`Fabius.pow_choose_two_add_mul_eq`, and
`Fabius.gaussianBinomial_q_lucas`.  The first two are natural-number
quadratic identities.  The coefficient, block, and phase lemmas prove
`[a*d+b,r*d+s]_ζ = choose(a,r) * [b,s]_ζ` when `0 < d`, `ζ` is a primitive
`d`-th root in a commutative integral domain, and `b,s < d`.  Its local
`two_mul_choose_two` helper is private; the unique public theorem of that name
belongs to `QChuVandermonde.lean`.

`JacobiTwoSquareCount.lean` is 0+4:
`Fabius.sumSqRep_two_eq_four_mul_twoSquareDivisorSum`,
`Fabius.sumSqRep_two_eq_four_mul_prod`,
`Fabius.theta_sq_eq_chi4_lambert`, and
`Fabius.theta_sq_eq_odd_lambert`.  It closes the nonzero two-square count and
instantiates both parameterized Lambert kernels from `TwoSquareTheorem.lean`.
The product theorem retains the even-valuation condition at every prime
divisor congruent to three modulo four; both Lambert identities are
unconditional over a complete normed field under `‖q‖ < 1`.

`CyclotomicDivisibility.lean` is 0+3:
`Fabius.cyclotomic_exponent_eq_one_iff`,
`Fabius.cyclotomic_dvd_gaussianBinomial_iff`, and
`Fabius.gaussianBinomial_mul_isPrimitiveRoot`.  For `k ≤ n` and `0 < d`, the
Gaussian cyclotomic exponent equals one exactly when `n % d < k % d`; over
`ℚ[X]` that is exactly the criterion for `Φ_d` to divide `[n,k]_X`.  In a
commutative integral domain, a primitive `n`-th root with `0 < n` gives
`[a*n,b*n]_ζ = choose(a,b)`.

`QCatalan.lean` is 1+11.  Its definition is `Fabius.qCatalan`; its theorems
are `Fabius.map_qInt`, `Fabius.qInt_X_monic`, `Fabius.qInt_X_natDegree`,
`Fabius.X_sub_one_mul_qInt`, `Fabius.qInt_X_eq_prod_cyclotomic`,
`Fabius.qInt_X_dvd_gaussianBinomial_rat`,
`Fabius.qInt_X_dvd_gaussianBinomial_int`,
`Fabius.qInt_X_mul_qCatalan`, `Fabius.qCatalan_natDegree`,
`Fabius.qCatalan_eval_one_mul`, and `Fabius.qCatalan_eval_one`.  Semiring
naturality and the commutative-ring q-integer identities yield
`[n+1]_X ∣ [2*n,n]_X` over `ℚ[X]` and `ℤ[X]`; the integral quotient has degree
`n*(n-1)`, satisfies `(n+1) C_n(1) = choose(2*n,n)`, and evaluates to the
ordinary Catalan number.

`NewtonInterpolation.lean` is 3+19.  Its definitions are
`Fabius.newtonCoeff`, `Fabius.nodeNewtonPoly`, and the compatibility alias
`Fabius.newtonInterpolant`; its theorems are
`Fabius.newtonCoeff_eq`, `Fabius.newtonCoeff_zero`,
`Fabius.newtonCoeff_mul_prod`, `Fabius.nodeNewtonPoly_succ`,
`Fabius.eval_nodeNewtonPoly`, `Fabius.degree_nodeNewtonPoly_lt`,
`Fabius.nodeNewtonPoly_eq_interpolate`,
`Fabius.eq_nodeNewtonPoly_of_eval_eq`,
`Fabius.coeff_nodeNewtonPoly_self`, `Fabius.newtonCoeff_eq_sum`,
`Fabius.nodal_range_pow`, `Fabius.prod_erase_pow_sub_pow`, and
`Fabius.newtonCoeff_pow_eq_sum`, together with compatibility forms
`Fabius.newtonPoly_succ`, `Fabius.eval_newtonPoly`,
`Fabius.degree_newtonPoly_lt`, `Fabius.newtonPoly_eq_interpolate`,
`Fabius.eq_newtonPoly_of_eval_eq`, and `Fabius.coeff_newtonPoly_self`.
Over a field these give triangular Newton
reconstruction, finite-node interpolation and uniqueness, divided differences,
and the geometric-power-node specialization, retaining each finite-node
injectivity, nonzero-product, `q ≠ 0`, and index hypothesis.  The node-qualified
family remains collision-free with `NewtonBasisGeneratingFunction.newtonPoly`;
the compatibility family is definitionally identical.

`QBetaIntegral.lean` is 1+8.  Its definition is `Fabius.qBeta`; its theorems
are `Fabius.qNumber_pos`, `Fabius.qBeta_term_eq`, `Fabius.qBeta_eq_prod`,
`Fabius.qBeta_eq_qGamma`, `Fabius.qBeta_comm`, `Fabius.qBeta_pos`,
`Fabius.qBeta_add_one_left`, and `Fabius.qBeta_add_one_right`.  Under
`0 < q < 1` and the displayed positive real arguments, they evaluate the
Jackson q-beta integral as an infinite-product and q-Gamma quotient and prove
symmetry, positivity, and both recurrences.

`GaussianBinomialBounds.lean` is 0+6.  Its exhaustive theorem surface is
`Fabius.gaussianBinomial_inv`, `Fabius.one_le_gaussianBinomial`,
`Fabius.finiteQPochhammerIn_pow_le_one`,
`Fabius.gaussianBinomial_le_inv_qPochhammerInfIn`,
`Fabius.pow_le_gaussianBinomial_of_one_lt`, and
`Fabius.gaussianBinomial_le_pow_div_of_one_lt`.  It evaluates Gaussian
palindromicity as field reciprocity, bounds coefficients uniformly for
`0 ≤ q < 1`, and transfers those bounds to the dimension-dominant regime
`Q > 1`; every nonzero-base, index, and order hypothesis remains explicit.
The proof reuses the stronger generic `Fabius.finiteQPochhammerIn_self_pos`
from `GeneralQConditionNumber.lean` rather than exporting a duplicate.

`EffectiveMonotoneInverse.lean` has exactly two public definitions,
`Fabius.SequentiallyComputableOn` and `Fabius.unitClamp`, and exactly six
public theorems: `Fabius.unitClamp_sequentiallyComputable`,
`Fabius.tolerantDifference_error`, `Fabius.tolerantDifference_safe_updates`,
`Fabius.tolerantDifference_inconclusive`,
`Fabius.tolerantBisection_correct`, and
`Fabius.effectiveInversionOn_Icc`.  Its natural-number controller performs
exactly `p` dyadic halvings at requested precision `p`; certified signed-code
comparisons update the bracket, while the third, inconclusive branch certifies
the current midpoint.  Doubling an accepted numerator through remaining
depths and using the final left endpoint in the no-hit case yield a uniform
dyadic name at denominator `2^p` with error at most `2^-p`.  The abstract Lean
theorem consumes a computable positive reciprocal inverse modulus.  The
adjacent `EffectiveGapInverse.lean` module constructs one from computable
positive rational dyadic-gap lower bounds and also derives effective uniform
continuity.

`EffectiveGapInverse.lean` has exactly eight public declarations:
`Fabius.EffectivelyUniformContinuousOn`, the structure
`Fabius.ComputablePositiveRationalSequence`,
`Fabius.ComputablePositiveRationalSequence.value`,
`Fabius.ComputablePositiveRationalSequence.reciprocalDenominator`,
`Fabius.ComputablePositiveRationalSequence.reciprocalDenominator_spec`,
`Fabius.inverseModulus_of_positiveRationalGap`,
`Fabius.effectiveInversionOn_Icc_of_computablePositiveRationalGap`, and
`Fabius.clampedEffectiveInversion_of_computablePositiveRationalGap`.  The
structure packages computable positive natural numerators and denominators.
Its reciprocal denominator is `denominator p / numerator p + 1`, whose
reciprocal lies strictly below the represented rational value.  For a strict
increasing inverse pair on `[0,1]`, the hypothesis is the uniform dyadic-gap
lower bound `α.value p ≤ f (x + 2^-p) - f x` for every
`x ∈ [0,1-2^-p]`.  With a computable dyadic oracle for `f` and interval maps
for both functions, the module proves sequential computability and effective
uniform continuity of `g` on `[0,1]`.  Its total computable-real-function
conclusion is exactly `fun x => g (unitClamp x)`: it agrees with `g` on the
unit interval but asserts nothing about the unclamped values of `g` outside it.

`FabiusInverseComputable.lean` has zero public definitions and exactly one
public theorem, `Fabius.fabiusInv_isComputableRealFunction`.  It instantiates
the generic realizer with the centered-spline dyadic oracle for `fabiusReal`
and `inverseFabiusDeltaDenominator`, clamps arbitrary input names without
changing the totalized inverse, and combines total sequential computability
with the logarithmic-Delta effective-uniform-continuity witness.  This closes
the total inverse computability certificate without asserting a practical
running-time or input-bit complexity bound.

The five-module q-calculus increment is exhaustively accounted for as follows.
`PolynomialQDerivative.lean` has the two definitions `qInt` and `qDerivative`
and the seventeen theorems `qInt_zero`, `qInt_one`, `qInt_succ`, `qInt_succ'`,
`qInt_add`, `qInt_one_left`, `one_sub_mul_qInt`, `qDerivative_apply`,
`qDerivative_monomial`, `qDerivative_C`, `qDerivative_X_pow`, `qDerivative_X`,
`qDerivative_C_mul_X_pow`, `eval_qDerivative_mul`,
`qDerivative_comp_C_mul_X`, `qDerivative_mul`, and `qDerivative_mul'`.
The q-integer definition and its first six laws need only a semiring;
`one_sub_mul_qInt` and the division-free evaluation identity use a commutative
ring; the coefficientwise linear map, monomial/scaling laws, and both product
rules use a commutative semiring.  Every nome is allowed, including zero and
one; there is no analytic-function or limiting derivative claim.

`PolynomialQLeibniz.lean` has no definition and the four theorems
`comp_C_mul_X_comp_C_mul_X`, `qDerivative_C_mul`,
`qDerivative_iterate_comp_C_mul_X`, and `qDerivative_iterate_mul`.  Every one
holds over an arbitrary commutative semiring, for arbitrary nome and every
natural iteration order including zero, with no division, topology, or
nonvanishing assumption.

`QPochhammerDerivative.lean` has no definition and the three theorems
`hasDerivAt_finiteQPochhammerIn`,
`hasDerivAt_finiteQPochhammerIn_of_ne_zero`, and
`hasDerivAt_finiteQPochhammerIn_comp`.  They work over every nontrivially
normed field with arbitrary nome and finite order.  The cofactor formula is
unconditional; the logarithmic rewrite assumes exactly that every displayed
factor is nonzero; the chain rule assumes exactly the supplied pointwise
`HasDerivAt`.  No infinite-product derivative is added.

`LambertSeriesLog.lean` has no definition and the four theorems
`one_le_norm_natCast_add_one`, `summable_lambert_series`,
`hasSum_lambert_log_complex`, and
`exp_neg_tsum_lambert_eq_qPochhammerInfIn`.  Apart from the unconditional
natural-cast norm helper, they assume exactly complex `a,q` with `‖a‖ < 1`
and `‖q‖ < 1`; they give absolute summability, the `HasSum` against principal
factor logarithms, and the branch-free exponential product identity.  They do
not assert a principal logarithm of the product, a norm-one boundary, or
analytic continuation.

`QGamma.lean` has the two total real definitions `qGamma` and `qNumber` and
the ten theorems `norm_lt_one_of_pos_of_lt_one`,
`qPochhammerInfIn_rpow_pos`, `qPochhammerInfIn_self_pos`, `qGamma_pos`,
`qGamma_one`, `qGamma_add_one`, `qGamma_nat_succ`, `qNumber_natCast`,
`qGamma_mul_qGamma_one_sub`, and `hasSum_theta_qGamma_reflection`.
Positivity, the value at one, recurrence, and natural factorial product use
`0 < q < 1`, with `0 < x` additionally where displayed.  The natural-cast
q-number bridge assumes only `q ≠ 1`; the totalized algebraic reflection
product assumes only `q < 1` and arbitrary real `x`; its theta `HasSum` form
assumes `0 < q < 1` and `0 < x < 1`.  This module supplies no complex
continuation, classical-gamma limit, pole, log-convexity, uniqueness, or
digamma result.

The valuation leaf `PrimePowerBinomialValuation.lean` now contributes no
definitions and exactly six theorems: `primePowerChoose_padicValNat_add`,
`primePowerChoose_padicValNat`, `primePowerSubOneChoose_padicValNat`,
`primePowerSubTwoChoose_padicValNat`, `twoPowChoose_padicValNat`, and
`twoPowSubTwoChoose_padicValNat`.  The first two are the additive and
subtraction forms for an arbitrary prime-power Pascal row.  The third says
every column `j < p^m` in row `p^m-1` is a `p`-adic unit, including `m = 0`.
The fourth identifies the row-`p^m-2`, column-`j-1` valuation with `v_p(j)`
under exactly `0 < j < p^m`; the last two are the strict-interior dyadic
specializations.  No valuation-histogram count is included.
The closed-form Gaunt leaf `LegendreGauntClosedForm.lean` contributes two definitions and
twenty-five theorems: the total integer zero-row Wigner-square datum, its exact
central-binomial and factorial forms, the all-degree Gaunt identification,
sharp support, positivity and vanishing criteria, and the product-linearization
coefficient bridge.  It makes no signed-symbol, phase, half-integer,
nonzero-magnetic-index, or general Wigner recoupling claim.  The baseline
also includes the three finite rational-entry, rational-matrix, and real-matrix
Wigner-square sum corollaries in `FabiusLegendreGauntClosedForm.lean`.  These
two new leaves therefore contribute thirty declarations in total.  The
two definitions are `legendreGauntAdmissible` and
`legendreWignerThreeJZeroSqRat`.  In source order, the twenty-five core theorem
names are `legendreGauntAdmissible_iff_exists_pairwise_add`,
`legendreGauntAdmissible_pairwise_add`,
`legendreWignerThreeJZeroSqRat_pairwise_add`,
`legendreWignerThreeJZeroSqRat_pairwise_add_factorial`,
`legendreWignerThreeJZeroSqRat_eq_factorial_of_halfSum`,
`legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible`,
`legendreGauntRat_add_boundary`,
`legendreGauntRat_add_boundary_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_zero_left`,
`legendreGauntRat_zero_left_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_pairwise_add_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_eq_zero_of_not_admissible`,
`legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGaunt_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreWignerThreeJZeroSqRat_pos_iff_admissible`,
`legendreWignerThreeJZeroSqRat_nonneg`,
`legendreWignerThreeJZeroSqRat_eq_zero_iff_not_admissible`,
`legendreGauntRat_pos_iff_admissible`,
`legendreGauntRat_eq_zero_iff_not_admissible`,
`legendreGaunt_pos_iff_admissible`,
`legendreGaunt_eq_zero_iff_not_admissible`, `legendreGauntRat_nonneg`,
`legendreGaunt_nonneg`,
`legendreProductLinearizationCoeffRat_eq_mul_wignerThreeJZeroSqRat`, and
`legendreProductLinearizationCoeffRat_pos_iff_admissible`.  The three wrapper
names are `rvachevLegendreGramEntryRat_eq_two_mul_sum_wignerThreeJZeroSqRat`,
`rvachevLegendreGramMatrixRat_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`, and
`upLegendreGramMatrix_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`.

The canonical fixed-nome inventory is `QPochhammerEntire.lean`: no public
definitions and exactly five public theorems,
`hasProdLocallyUniformly_complexQPochhammerInf`,
`complexQPochhammerInf_differentiable`,
`complexQPochhammerInf_eq_zero_iff`,
`complexQPochhammerInf_eq_zero_iff_eq_inv_pow`,
and `analyticOrderAt_complexQPochhammerInf_of_eq_zero`.  For a fixed complex
strict contraction `q`, they give locally uniform convergence in the symbol
variable, entireness, the division-free factor-zero criterion, the exact
reciprocal-power zero lattice when `q ≠ 0`, and analytic order one at every
zero under the historical complex-product name.  The raw factor criterion and
order theorem include `q = 0`; the generic-name analytic-order theorem is
owned by `QPochhammerInfinite.lean`.  No joint holomorphy,
outside-disk reciprocal formula, or centered characteristic-function/MGF
package is counted in this leaf.  The separately counted
`GeometricPochhammerNormalConvergence.lean` leaf is 0+3 and supplies the
outer spectral-product locally uniform theorem and its dyadic/Fabius
specializations, but none of those remaining compound spectral clauses.

The same merged tree adds the complementary general q-product leaves.
`QPochhammerDissection.lean` contributes no definitions and two theorems,
`finiteQPochhammerIn_dissection` and
`finiteQPochhammerIn_dissection_remainder`, for exact full-period and remainder
residue-class decompositions over an arbitrary commutative ring.
`QPochhammerInfinite.lean` contributes one definition and twenty-nine
theorems.  Its surface includes convergence and finite-prefix limits in
complete normed commutative rings, concatenation and residue-class dissection,
factor and reciprocal-power zero criteria, locally uniform parameter
convergence and continuity over complete locally compact normed fields, and
entireness with explicit nonzero derivatives and analytic order one at every
factor zero over `ℂ`, including `q=0`.  These two leaves therefore contribute
thirty-two declarations.  Their
generic `qPochhammerInfIn` is distinct from the older
`complexQPochhammerInf`; the five-theorem `QPochhammerEntire` API above remains
the legacy compatibility layer, while the generic analytic-order theorem is
canonically owned by `QPochhammerInfinite`.  The named equality bridge
`complexQPochhammerInf_eq_qPochhammerInfIn` is counted in the separate
one-definition/ten-theorem `RvachevPochhammerFactorization.lean` surface.

The synchronized q-series API also retains the full `origin/main` theorem
inventory.  `GaussianBinomialAtNegOneDerivative.lean` is 0+5, including the
commutative-semiring evaluation theorem `gaussianBinomial_X_eval`, and
`GaussianBinomialContinuity.lean` is 0+3:
`continuous_gaussianBinomial`, `tendsto_gaussianBinomial_nhds_one`, and
`gaussianBinomial_eq_finiteQPochhammerIn_div`.
`GaussianBinomialPalindromic.lean` is 0+14:
`reflect_add_of_natDegree_le`, `reflect_one'`,
`gaussianBinomial_natDegree_le`, `gaussianBinomial_zero_left`,
`gaussianBinomial_diag'`, `reflect_gaussianBinomial`,
`coeff_gaussianBinomial_reflect`, `coeff_gaussianBinomial_zero`,
`coeff_gaussianBinomial_top`, `gaussianBinomial_natDegree`,
`gaussianBinomial_monic`, `two_mul_derivative_gaussianBinomial_eval_one`,
`coeff_gaussianBinomial_one_of_pos_of_lt`, and
`coeff_gaussianBinomial_one`.
`GaussianBinomialPolynomialStructure.lean` is 0+5:
`natDegree_gaussianBinomial_universal`,
`gaussianBinomial_universal_monic`,
`coeff_zero_gaussianBinomial_universal`,
`gaussianBinomial_universal_reflect`, and
`coeff_gaussianBinomial_universal_symm`.
`CentralQBinomialReduction.lean` is 0+6: `finiteQPochhammerIn_mul_neg`,
`finiteQPochhammerIn_two_mul`, `finiteQPochhammerIn_map_ringHom`,
`central_gaussianBinomial_sq_mul_int`, `central_gaussianBinomial_sq_mul`,
and `central_gaussianBinomial_sq_div`.  `CyclotomicFactorization.lean` is
0+7: `div_add_div_le_div`, `div_le_div_add_div_add_one`,
`mem_range_and_mem_divisors_iff`, `finiteQPochhammerIn_X_eq_prod_cyclotomic`,
`finiteQPochhammerIn_X_eq_gaussianBinomial_mul`,
`prod_cyclotomic_pow_div_extend`, and
`gaussianBinomial_X_eq_prod_cyclotomic`.  The
`PrimitiveRootBlock.lean` 0+3, `QLucas.lean` 0+7,
`CyclotomicDivisibility.lean` 0+3, and `QCatalan.lean` 1+11 surfaces are
listed exhaustively above.  The
`NewtonInterpolation.lean` 3+19 and `QBetaIntegral.lean` 1+8 surfaces are
also listed exhaustively above.  The
`JacobiTripleProduct.lean` 2-definition/25-theorem tranche contains the finite triple-product
polynomial and field identities, the bilateral Jacobi `HasSum` forms, and the
pentagonal and paired-pentagonal `HasSum` corollaries.  The
`QBinomialTheoremInfinite.lean` has one public definition and 29 public theorems.
Its retained and strengthened surface includes the comparison and norm bounds,
fixed-column Gaussian limits and rates, Euler product, analytic q-binomial and
reciprocal Euler `HasSum` results,
`norm_finiteQPochhammerIn_pow_sub_one_le_exp_of_norm_le_one`, both
`tendsto_gaussianBinomial_add_const_atTop` and the compatibility alias
`tendsto_gaussianBinomial_add_atTop`, and the effective `IsBigO` bounds.
The companion `GaussianBinomialFixedColumnRate.lean` surface is 0+9:
`norm_finiteQPochhammerIn_pow_sub_one_le_exp'`,
`norm_finiteQPochhammerIn_pow_sub_one_le`,
`norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le`,
`norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le`,
`norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le`,
`gaussianBinomial_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_shifted_fixedColumn_relativeError_isBigO`,
`gaussianBinomial_fixedColumn_error_isBigO`, and
`gaussianBinomial_shifted_fixedColumn_error_isBigO`.  The unprimed
exponential bound and both fixed/shifted limit names remain canonically owned
by `QBinomialTheoremInfinite.lean`.  `QPascalSummation.lean` is 0+4:
`sum_gaussianBinomial_succ_mul`, `sum_gaussianBinomial_succ_mul'`,
`Commute.gaussianBinomial_left`, and `Commute.gaussianBinomial_right`.
`QuantumBinomial.lean` is 0+2, namely `quantumPlane_mul_pow` and
`quantum_binomial`.  Finally, the `RogersSzegoPolynomial.lean` 1-definition/9-theorem
tranche covers the zero, row-sum, and successor laws, dilation and three-term
recurrences, the Euler antidiagonal convolution, and
`hasSum_rogersSzego_generating`.  None of these retained APIs is replaced by
the fixed-nome `QPochhammerEntire` layer.

The eight-module increment is exhaustive and contributes 60 public
declarations.  The 0+5 `GaussianBinomialPolynomialStructure.lean` inventory is
listed immediately above.  `GaussianBinomialPalindromic.lean` is 0+14:
`reflect_add_of_natDegree_le`, `reflect_one'`,
`gaussianBinomial_natDegree_le`, `gaussianBinomial_zero_left`,
`gaussianBinomial_diag'`, `reflect_gaussianBinomial`,
`coeff_gaussianBinomial_reflect`, `coeff_gaussianBinomial_zero`,
`coeff_gaussianBinomial_top`, `gaussianBinomial_natDegree`,
`gaussianBinomial_monic`, and
`two_mul_derivative_gaussianBinomial_eval_one`,
`coeff_gaussianBinomial_one_of_pos_of_lt`, and
`coeff_gaussianBinomial_one`.  Its degree bound,
palindromicity, endpoint coefficients, and division-free mean identity hold
over a commutative semiring under exactly `k ≤ n`; coefficient reversal also
uses `j ≤ k*(n-k)`, and exact degree and monicity add `Nontrivial R`.  It does
identify the coefficient of `q` as one under exactly `0 < k < n`, with a
total if-and-only-if classifier covering both boundary and out-of-range cases.

`QExponential.lean` is 3+8.  Its definitions are `qDeriv`, `qExp`, and
`qExpBig`; its theorems are `qFactorial_mul_one_sub_pow`,
`qFactorial_ne_zero`, `qDeriv_mul`, `hasSum_qExp`, `hasSum_qExpBig`,
`qExp_mul_qExpBig_neg`, `qDeriv_qExp`, and `qDeriv_qExpBig`.  The factorial
clearing identity is ring algebra and the function product rule is total.
The series and eigenfunction laws work over a complete normed field under
`‖q‖ < 1`; the small exponential additionally uses
`‖(1-q)*x‖ < 1`, while both eigenfunction statements assume `x ≠ 0`.
`JacksonIntegral.lean` is 1+7: `jacksonIntegral`;
`qDeriv_jacksonIntegral`, `one_sub_mul_pow_mul_qDeriv`,
`tendsto_jackson_sum_qDeriv`, `jacksonIntegral_qDeriv`,
`tendsto_jackson_sum_parts`, `jackson_parts_of_tendsto`, and
`jacksonIntegral_mul_qDeriv`.  The first fundamental theorem assumes exactly
`q ≠ 1`, `x ≠ 0`, and summability of the displayed Jackson series.  The
telescoping identity is unconditional; partial-sum forms use the stated limit,
and `jacksonIntegral` forms add summability.

`ThetaQuasiPeriodicity.lean` is 1+6: `bilateralTheta`;
`thetaExponent_add_one`, `pow_thetaExponent_add_one`,
`hasSum_bilateralTheta`, `bilateralTheta_eq_prod`,
`bilateralTheta_mul_left`, and `bilateralTheta_eq_zero_iff`.  Its sum and
product require a complete normed field, `‖q‖ < 1`, and `z ≠ 0`;
quasi-periodicity and the exact lattice `z = -q^m` additionally require
`q ≠ 0`.  `JacobiCubic.lean` is 0+2:
`two_mul_add_one_le_three_pow` and `hasSum_jacobi_cubic`; the second gives the
complex cubic identity in `HasSum` form under exactly `‖q‖ < 1`.

`QPochhammerLogDerivative.lean` is 0+10:
`one_sub_le_norm_one_sub_mul_pow`,
`summable_pow_div_one_sub_mul_pow`, `summable_log_one_sub_mul_pow`,
`one_sub_mul_pow_ne_zero`, `qPochhammerInfIn_eq_cexp_tsum_log`,
`hasDerivAt_tsum_log_one_sub_mul_pow`,
`hasDerivAt_qPochhammerInfIn`, `hasDerivAt_lambert_series`,
`tsum_neg_pow_div_one_sub_mul_pow_eq`, and
`hasDerivAt_qPochhammerInfIn_lambert`.  The logarithm series is summable for
every complex `a` when `‖q‖ < 1`; reciprocal-factor summability and both final
product derivatives use `‖a‖ < 1`, with termwise differentiation established
on every disk `‖a‖ < r < 1`.  `QPochhammerOrderDerivative.lean` is 0+3:
`hasDerivAt_const_cpow'`, `hasDerivAt_qPochhammerInfIn_mul_cpow`, and
`hasDerivAt_qPochhammerC`.  The first assumes `q ≠ 0`; the latter two assume
exactly `‖q‖ < 1`, `q ≠ 0`, and `‖a*q^α‖ < 1`.  None of these derivative
leaves claims a nome derivative, boundary continuation, or branch-independent
complex-order coordinate.

The cumulative seven-module closure is also exhaustive.  The already listed
`GeneralizedRvachevIdentifiability.lean` contributes `0+6` declarations.
`GeometricPochhammerNormalConvergence.lean` contributes no definitions and
three theorems:
`hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`,
`hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`, and
`hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf`.  The first
assumes exactly complex `‖q‖ < 1` and proves locally uniform convergence on all
of `ℂ` of the outer Pochhammer product, including `q = 0`; the second is the
unconditional dyadic specialization and the third additionally assumes a
bounded Fabius witness and `IsFabius`.  It proves no joint normality in `(q,z)`
or boundary theorem at `‖q‖ = 1`.

`ClassicalPochhammerLimit.lean` contributes no definitions and five theorems:
`ascPochhammer_eval_eq_prod_range`,
`tendsto_one_sub_div_one_sub_of_hasDerivAt`,
`tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt`,
`tendsto_finiteQPochhammerIn_cpow_div_pow`, and
`tendsto_finiteQPochhammerIn_rpow_div_pow`.  The rising-product identity is
commutative-semiring algebra.  The generic punctured-neighborhood limit works
over every nontrivially normed field under exactly `HasDerivAt f c 1` and
`f 1 = 1`; the complex-principal-power and real-power forms are valid for
every exponent and finite order.  No rate, uniformity, infinite-product limit,
or classical-gamma limit is counted.

`GaussianBinomialUniversal.lean` contributes no definitions and exactly two
theorems, `gaussianBinomial_eq_eval₂_universal` and
`gaussianBinomial_eq_eval_map_universal`.  Over every commutative semiring and
for arbitrary `q,n,k`, they identify `[n,k]_q` with evaluation of the universal
polynomial in `ℕ[X]`, directly or after coefficient mapping.  No degree,
unimodality, log-concavity, or factorization result is added.

`PolynomialQTaylor.lean` contributes two definitions, `qFactorial` and
`qFallingPower`, and eighteen theorems: `qFactorial_zero`,
`qFactorial_succ`, `qDerivative_one`, `qDerivative_iterate_add`,
`qDerivative_iterate_C_mul`, `qDerivative_iterate_sum`,
`qDerivative_iterate_C_mul_X_pow`,
`qDerivative_iterate_eq_zero_of_natDegree_le`, `qFallingPower_zero`,
`qFallingPower_succ`, `qFallingPower_succ'`, `qFallingPower_monic`,
`qFallingPower_natDegree`, `qFallingPower_eval_self`,
`qDerivative_qFallingPower_succ`, `qDerivative_iterate_qFallingPower`,
`prod_qInt_sub_eq_qFactorial`, and `qTaylor`.  The factorial and iterator
algebra are commutative-semiring results, the falling-power layer is over a
commutative ring, and exact degree also assumes nontriviality.  The field-valued
Taylor theorem assumes exactly `[j]_q ≠ 0` for `1 ≤ j ≤ N` and
`f.natDegree ≤ N`.  It is a finite polynomial identity, not an analytic
expansion, remainder estimate, convergence theorem, or `q → 1` result.

`QPartialFractions.lean` contributes the definition `partialFractionCoeff` and
five theorems: `prod_erase_one_sub_inv_pow_mul_pow`,
`finiteQPochhammerIn_self_ne_zero_of_le`,
`partialFractionCoeff_mul_prod_eq_one`,
`sum_partialFractionCoeff_mul_prod_erase`, and
`one_div_finiteQPochhammerIn_eq_sum`.  Over a field, `(q;q)_n ≠ 0` suffices for
the polynomial identity and includes `q = 0`; the pointwise reciprocal formula
also assumes every displayed pole factor nonzero.  The two normalization
helpers state their explicit `q ≠ 0` and index hypotheses.  There is no
infinite expansion, repeated-pole theory, or convergence claim.

`QPochhammerIntegerIndex.lean` contributes the definitions `qIntervalProd` and
`finiteQPochhammerZ` and fifteen theorems: `Ico_int_eq_image_range`,
`prod_Ico_int_eq_prod_range`, `qIntervalProd_of_le`, `qIntervalProd_of_lt`,
`qIntervalProd_self`, `qIntervalProd_symm`, `qIntervalProd_trans_of_le`,
`qIntervalProd_trans`, `finiteQPochhammerZ_natCast`,
`finiteQPochhammerZ_neg_natCast`, `prod_Ico_add_zpow`,
`qIntervalProd_add_eq`, `finiteQPochhammerZ_add`,
`finiteQPochhammerZ_add_one`, and `finiteQPochhammerZ_neg_natCast_eq`.
The ordered cocycle is unconditional; the all-order cocycle assumes its two
factors nonzero.  Translation and concatenation require `q ≠ 0`, concatenation
also requires both factors nonzero, the one-step shift requires its two
displayed nonzero factors, and the closed negative-index form requires
`a ≠ 0` and `q ≠ 0`.  Empty intervals and natural/negative-natural indices are
included; no continuation in the index or root-of-unity regularization is
claimed.

The audited formula contract is equally exact.  Admissibility is even total
degree plus the three weak triangle inequalities, equivalently
`i=b+c`, `j=a+c`, `k=a+b`.  If `C_n=choose (2*n) n` and `s=a+b+c`, then the
square datum is zero off support and
`W²(b+c,a+c,a+b)=C_a*C_b*C_c/((2*s+1)*C_s)`; factorially this is
`s!^2*(2*a)!*(2*b)!*(2*c)!/((2*s+1)!*a!^2*b!^2*c!^2)`.  The half-sum theorem
assumes exactly `i+j+k=2*s` and `i≤s`, `j≤s`, `k≤s`.  The two named boundaries
are `G_Q(i,j,i+j)=2*C_i*C_j/((2*(i+j)+1)*C_(i+j))=2*W²(i,j,i+j)` and
`G_Q(0,j,k)=(if j=k then 2/(2*j+1) else 0)=2*W²(0,j,k)`.  At every natural
triple `G_Q=2*W²`, its real counterpart is twice the real cast, positivity is
equivalent to admissibility, vanishing is equivalent to nonadmissibility, and
all three forms are nonnegative.  The rational product coefficient is
`(2*k+1)*W²` and is positive exactly on support.  Both rational finite-Gram
wrappers are the unconditional twice-sum
`2*∑ r∈range ((i+j)/2+1), c_r*W²(i,j,2*r)`; the real wrapper has the same finite
form and assumes exactly `F : BoundedFabius` and `hF : IsFabius F`.

This square datum is not a bridge to a separately implemented general Wigner
symbol.  No signed value or phase convention, half-integer or
nonzero-magnetic-index API, general `3j`/`6j`/`9j`, orthogonality, recoupling,
or named Wigner-symmetry theorem is present.  The Gaunt factorial identity and
product-coefficient nonnegativity/zero criteria are composable but do not have
separate named wrappers.  Infinite Legendre interchange, Christoffel
reconstruction, roots/quadrature, Padé/J-fractions, infinite Jacobi theory, and
asymptotics remain open.

The New Frontiers finite Gram--Legendre crosswalk consequently has eleven modules,
twenty definitions, and 109 theorems, hence 129 public declarations; its
predecessor nine-module subtotal was `18+81=99`, and the two closed-form leaves
contribute `2+25` and `0+3`.  The integer-index zero-row square datum and finite
Wigner-square Gram route are closed, while signed/phase, half-integer,
nonzero-magnetic-index, general Wigner/recoupling, and later infinite spectral
layers remain outside this tranche.  The live baseline records zero missing
headers and zero missing doc comments.  Future source additions must preserve
both zero-gap invariants.  Run the script for live numbers after merging
concurrent source work.

The additional declaration in `PolynomialCombExactness.lean` is
`integral_polynomial_mul_rvachevUp_eq_dyadic_tsum`, the exact normalized
physical-coordinate self-sampling quadrature for every real polynomial whose
natural degree is at most the dyadic level and every real phase.

The effective-inverse union contributes three modules and seventeen public
declarations.  `EffectiveMonotoneInverse.lean` is exactly 2+6: the definitions
`SequentiallyComputableOn` and `unitClamp`; the clamping theorem
`unitClamp_sequentiallyComputable`; the three certified tolerant-comparison
lemmas `tolerantDifference_error`, `tolerantDifference_safe_updates`, and
`tolerantDifference_inconclusive`; and the constructive inverse results
`tolerantBisection_correct` and `effectiveInversionOn_Icc`.  The latter works
for a computably dyadically approximable strict monotone bijection of
`[0,1]` supplied with a computable positive reciprocal inverse modulus; its
three-way comparison never decides equality, because the inconclusive branch
already certifies the requested inverse error.  `FabiusInverseComputable.lean`
is exactly 0+1: `fabiusInv_isComputableRealFunction` combines that sequential
realizer with the logarithmic Delta modulus for every bounded Fabius witness.
Clamping makes the theorem about the total inverse on all real inputs.  These
results are computability certificates, not an input-bit running-time bound or
an exact least endpoint-mass denominator.  The third module,
`EffectiveGapInverse.lean`, contributes 4+4, the eight declarations listed
above, and supplies the generic rational-gap-to-modulus bridge; its clamped
extension boundary remains explicit.

**Deferred publication status.**  The fixed-26 publication check—14 fresh build
cycles and 12 retained verified pairs—is recorded once in the
[draft manifest](semi-formalized-research-frontiers/drafts/MANIFEST.md#fixed-26-publication-checkpoint).
A row still marked pending makes no synchronization claim.  The exact older
receipts below remain historical evidence; under the user-directed deferral,
the fixed-26 table is an inventory rather than a merged-current parity receipt.

Four direct artifact receipts record the last synchronized pre-9135 source/PDF
pairs and are now historical because the live sources include the new
q-Chu/reversal, geometric-generating, Gaussian second-moment, and Lambert
branch-gap Bernoulli APIs.  The primary receipt is a
14,037-line, 702,119-byte TeX source
(SHA-256
`6a20e02cf300c0b29ba8d175831b4f86e4b336601cc5bd5f5752d5c5889be69a`)
and a 197-page, 1,602,500-byte PDF (SHA-256
`f083cd78308aba99d23d42372786c4b0a946ea8f5d47445c44d664fccfdde5e3`).
The Lean-walkthrough receipt is a 6,598-line, 465,231-byte TeX source (SHA-256
`796dd849fa423ba07413eaf0a1f30dc608355c5a3cd877aa7409ad089c54794e`)
and a 149-page, 1,231,442-byte PDF (SHA-256
`bc6e3e716a1a10daf24a065f6c97e2d00cbc95071ada777050a95f91598db4a0`).
The canonical-frontier receipt is a 17,954-line, 813,297-byte TeX source
(SHA-256
`bcd9eefce2ead08e2cbb283e091a859aa31f36c67416543e994e10e8f9db3075`)
and a 262-page, 1,885,642-byte PDF (SHA-256
`7f7e1279e38c766a465e640638ea7e0079a942de0bc84a5c22be497af27c7bab`).
The q-series receipt is a 16,834-line, 837,715-byte TeX source (SHA-256
`4785625c1399558f3ca59481888fc76514e0a327a1faa16945c61851f874f3d5`)
and a 395-page, 2,494,961-byte PDF (SHA-256
`89159b2635f489a42d4c972fac95332808b1d637dee7921085db1ed7d6e055af`).
Their exact successful three-pass page sequences were respectively
194→197→197, 144→149→149, 254→262→262, and 386→395→395.  Primary and
walkthrough logs and publication gates are clean; the frontier retains only
expected underfull diagnostics, and the q-series master retains one harmless,
readable 32.5659 pt overfull line.  All page, metadata, font, render, text,
and representative-visual gates passed.  These receipts certify their named
pre-9135 pairs only and are superseded by the synchronized 2026-09-04 receipts
below.

The independently scoped Sequence publication remains current.  The Lambert
guide's preceding synchronized receipt is a 4,829-line, 174,423-byte TeX with SHA-256
`724dfe5b1effcda29325a5bdfb066ff970eb74ab460f650185339fefce40ebc1`;
its 69-page, 952,929-byte PDF has SHA-256
`0b5f28dbfe590658e74150e8ccff6f023ecd0b8fb4e3e978ec275d9ddd244de6`.
Its successful page sequence was 67→69→69; machine and visual gates passed,
with expected underfull diagnostics and one harmless readable 0.825 pt
internal overfull line.  The Bernoulli-series source overlay made that Lambert
PDF historical; the synchronized 2026-09-04 receipt below supersedes it.  The
Sequence inversion/transseries volume's
16,705-line, 778,477-byte TeX has SHA-256
`4aa038c10ddd931b7c1248095ddfdf0ce8769c69cc0df4f344f6365d0e45e8e1`;
its 205-page, 2,198,655-byte PDF has SHA-256
`ec1f4d2ac608786f33be97d040fdfd03b6f74494dee74f044fd2e6631217d4fb`.
Its successful page sequence was 198→205→205; corrected title/author metadata,
machine gates, and extensive visual checks passed.  The final log retains one
duplicate-page-destination notice, nine PDF-string notices, 47 overfull and
12 underfull diagnostics; sampled largest cases are clean and unclipped.

**Historical synchronized publication receipts (2026-09-04).** Each pass tuple
below is `pages/bytes`.  At their named source checkpoints, all six TeX/PDF
pairs completed exactly three
successful serial halt-on-error passes from absent sidecars.  Final-log
reference/rerun/error checks, metadata, A4 rotation zero, every-page render and
nonblank-text checks, embedded/subset fonts with Libertinus and no Type 3, and
representative visual checks all passed; generated sidecars were cleaned and
forbidden checksum-ledger basenames were absent.  These six pairs remain
historical receipts for their named source checkpoints; the later historical
`b899` receipts below superseded them where a rebuilt root was listed.

- Primary exposition: TeX 14,328 lines / 715,760 bytes / SHA-256
  `60c0a6ff4e75ec37e6928067859671d87622ad8f430a1006dd4c71c7e7b25674`;
  passes 197/1,579,558 → 200/1,621,473 → 200/1,621,467; final PDF 200 pages /
  1,621,467 bytes / SHA-256
  `50febffeb7dda743330bd346b8f5fd45f85668db97c19fb52d4cd741d1692826`;
  fonts 29 total / 6 Libertinus / 0 Type 3.
- Lean walkthrough: TeX 6,855 lines / 482,759 bytes / SHA-256
  `1c48c54b194eb9e99dae64ddca70e2aa5d2edd995160ee2d5bc6455b545683f7`;
  passes 149/1,225,017 → 154/1,262,552 → 154/1,262,574; final PDF 154 pages /
  1,262,574 bytes / SHA-256
  `f9cba79348ffb81c41fc08b6523548effcc45ded9a2eb2b18e618ac9d59d0648`;
  fonts 30 / 7 / 0.
- Lambert Guide: TeX 4,876 lines / 177,511 bytes / SHA-256
  `d852a345685dd61335a89fc4fd1092680bdc597a5d1e6ac612883946ad0d99ea`;
  passes 68/963,230 → 70/986,865 → 70/986,865; final PDF 70 pages /
  986,865 bytes / SHA-256
  `0b8801649a6dd43d9f02dcfc2f60cac50b5c8f88bd782645bf97d30cc3dfbd41`;
  fonts 42 / 5 / 0; one harmless readable 0.82504 pt overfull and 133
  underfull diagnostics.
- Canonical frontier: TeX 18,173 lines / 826,738 bytes / SHA-256
  `844842bf699a24651f660bd7d81d814f6396b4fe6fc6de66a04908904221860b`;
  passes 257/1,822,725 → 265/1,904,567 → 265/1,904,551; final PDF 265 pages /
  1,904,551 bytes / SHA-256
  `dcaa7ac1e5397912c97a474b4023521e49d0785eb6ef67d83d0ce002d9cbb6e6`;
  fonts 40 / 8 / 0; one readable unclipped 9.43108 pt overfull at source
  lines 1032–1043 and 299 underfull diagnostics.
- Geometric q-frontier: TeX 27,598 lines / 1,270,870 bytes / SHA-256
  `6db4e211b0588ed75a0e89e13d97306f1d5d38b42a2bf941914ea16b9ca93dae`;
  passes 386/8,157,293 → 403/8,339,780 → 403/8,339,736; final PDF 403 pages /
  8,339,736 bytes / SHA-256
  `4d909b5e228e2053d473dc75da502382c7a4fe2b096f798e124e6530d3a15027`;
  fonts 43 / 11 / 0; zero overfull and 37 underfull diagnostics.
- Canonical q-series synthesis: TeX 16,910 lines / 842,514 bytes / SHA-256
  `196f219d5e1efba463ebabb69659697b1afb28989ef1a8da6219226d3262ad32`;
  passes 390/2,386,364 → 398/2,501,624 → 398/2,501,638; final PDF 398 pages /
  2,501,638 bytes / SHA-256
  `e8094b054f52b1fb71c7540f0834155fae0eac17887cb7cac1567848bd65d3b3`;
  fonts 43 / 5 / 0.  Every pass's index run accepted 164 entries, rejected none,
  produced 254 lines, and emitted no warning.  The sole retained 32.5659 pt
  overfull paragraph at source lines 590–598 is readable and unclipped; the
  final log has zero underfull diagnostics.

**Historical `b899` synchronized publication receipts (2026-09-04).** Each pass
tuple below is `pages/bytes`.  All ten roots were frozen and built in exactly
three serial halt-on-error passes from absent sidecars.  Subsequent merged
source changes make these receipts historical; the deferred rebuild inventory
is recorded in the fixed-26 checkpoint linked above.

- Primary exposition: TeX 15,148 lines / 759,509 bytes / SHA-256
  `721cb901de2254ef48991452c4831762f54a36e0a405b4bbeb7f812653e71754`;
  passes 208/1,640,077 → 210/1,683,143 → 210/1,683,141; final PDF
  210 pages / 1,683,141 bytes / SHA-256
  `afe85efec5716fe85cc7d8a5d6af459fd72775526f4bda11df04e6ff275b36c9`;
  fonts 29 total / 6 Libertinus / 0 Type 3.
- Lean walkthrough: TeX 7,260 lines / 526,929 bytes / SHA-256
  `2005d4a70a66a1d8f3eac9be6d83585ea70c9312b09b098f2c65025db9fca814`;
  passes 160/1,281,609 → 165/1,319,585 → 165/1,319,594; final PDF
  165 pages / 1,319,594 bytes / SHA-256
  `b5e886d7c76db56fd9e9e1552bdd78fbd65ea9075ea1e04d62c00a7c04e948fb`;
  fonts 30 / 7 / 0.
- Geometric q-frontier: driver 27,671 lines / 1,275,367 bytes / SHA-256
  `d47c0ad93eb359d13e7e9772668f16dbc98bcb4d880f3679366e1d461451bbcd`;
  recursive TeX closure 8 files / 27,777 lines / 1,281,413 bytes / digest
  `39f7cd41e706314f2cafb903c2da2e6e83d2b17f5bb0612492204d15c1a28d91`;
  passes 388/8,163,847 → 405/8,346,265 → 405/8,346,247; final PDF
  405 pages / 8,346,247 bytes / SHA-256
  `fef7d8260543ad1d20d69e9e41fa0cfc31603de7961f6aeb97a50740aecd596c`;
  fonts 43 / 11 / 0.
- Canonical q-series synthesis: driver 17,265 lines / 864,659 bytes / SHA-256
  `4dd3f7fb22387d8e3d039e8d49cd870a63ebe0881f7f215c7074854825a27bb9`;
  recursive TeX closure 14 files / 26,762 lines / 1,210,902 bytes / digest
  `b567430fdd64f6d50bd24fcb070216c27f7e3e81e8b0c76c3228767ebdf980c6`;
  passes 397/2,417,476 → 405/2,533,717 → 405/2,533,715; final PDF
  405 pages / 2,533,715 bytes / SHA-256
  `055eb1fc26467857394a5b3bd8cd327f6985ea5d2f966ab5f099ac20bb2b8fb2`;
  fonts 43 / 5 / 0; every pass's index run accepted 164 entries, rejected
  none, produced 254 lines, and emitted no warning.
- Inverse-theory synthesis: driver 293 lines / 11,514 bytes / SHA-256
  `92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c`;
  recursive TeX closure 17 files / 10,682 lines / 431,748 bytes / digest
  `6e4e6fde424fd5046467b1f1cec0c19b6c10eb681fae4ba7cc53e14b6a5bf61e`;
  passes 132/1,983,313 → 137/2,045,485 → 137/2,045,486; final PDF
  137 pages / 2,045,486 bytes / SHA-256
  `cee0de894656562fbdb75d6304055fc03fae06203985119419e465a5cd213995`;
  fonts 31 / 6 / 0.
- Comb-interpolation synthesis: driver 187 lines / 6,724 bytes / SHA-256
  `a4c1e33165ff7291682cd890f23fe4af98e9f11f7ad1d9a7f8b68c78d53f9a56`;
  recursive TeX closure 15 files / 12,597 lines / 477,163 bytes / digest
  `9e22455b3f65eb48306ad21c57445b6052a56498cb363666ffb9b160f5cc8090`;
  passes 153/2,383,950 → 160/2,467,995 → 160/2,468,000; final PDF
  160 pages / 2,468,000 bytes / SHA-256
  `ad8587049580e6fde371f534b6f8b4e56fa4c929173f87d3021ed369e5225d4c`;
  fonts 33 / 7 / 0.
- Lambert Guide: TeX 4,940 lines / 181,577 bytes / SHA-256
  `2e6a4782fc4e4b945869f5fb45b39cf94e8dc34296866edf26b4cdfe19b1898b`;
  passes 68/968,083 → 70/991,847 → 70/991,848; final PDF 70 pages /
  991,848 bytes / SHA-256
  `f802d78299f8f6aca7d31b935a4884f9343389a7307decb04c18b5159c8a4f04`;
  fonts 42 / 5 / 0.
- Up Polynomial Synthesis: driver 2,368 lines / 98,609 bytes / SHA-256
  `95d293e34559e910cca2df4547e6e181a8d26bc8e8cf61c4445cf12c57ed8e0e`;
  four-file TeX closure 5,434 lines / 211,270 bytes / digest
  `62aa76428089cd164705b1d31e038d4e48545681eedc01cb491e6a94f07b0e41`;
  passes 61/1,045,488 → 62/1,071,179 → 62/1,071,181; final PDF
  62 pages / 1,071,181 bytes / SHA-256
  `99c5d8256b983652755fe8e46ef015277e61b94941a4ca6c875bddaf0493b101`;
  fonts 27 / 4 / 0.
- Thue--Morse Atlas: TeX 10,553 lines / 481,614 bytes / SHA-256
  `cced4128c359ec467baaf1a55c21c68424397f783a39ea7fe2af5a94975b9dd5`;
  passes 139/1,681,559 → 144/1,739,891 → 144/1,739,884; final PDF
  144 pages / 1,739,884 bytes / SHA-256
  `1c81863b0976017fab1b7f5972c50cd541b3ffb05306bf85994548a56a782fc0`;
  fonts 38 / 8 / 0.
- Canonical semi-formalized frontier: TeX 18,651 lines / 858,502 bytes /
  SHA-256
  `140256058b7a01bcdb4f1592cfab9e6c2ac170f5f0863572627a9b2f93ab7793`;
  passes 265/1,868,249 → 273/1,950,120 → 273/1,950,112; final PDF
  273 pages / 1,950,112 bytes / SHA-256
  `17525c7623bf774f515ecf1a949d533bbe125fde036356c4bb9f787eedad0322`;
  fonts 40 / 8 / 0.

Across all ten roots, required final-log error/reference/rerun
gates, metadata, A4/rotation-zero checks, every-page render and nonblank-text
checks, embedded/subset fonts with Libertinus and no Type 3, representative
visual checks, sidecar cleanup, and the forbidden-checksum-basename search all
passed. Diagnostics are clean except for five minor q-series horizontal boxes
(maximum 10.14 pt), two inverse horizontal boxes (2.42 and 2.45 pt), one
Lambert horizontal box (0.83 pt), and one canonical-frontier horizontal box
(9.43108 pt), all nonblocking. The final aggregate TeX closure contains 76
files / 140,223 lines / 6,439,569 bytes, with direct aggregate digest
`ae8690ad8d160055cbae36eff96d858f87572d171e7aacf7540d67543998af21`.
All ten rows were synchronized at the named `b899` checkpoint; they and the
earlier receipts below remain historical provenance for their named sources.

The B2--B11 publication roots retain exact synchronized or historical receipts
at their named checkpoints. Their pass, byte-progression, font, and common-gate records are kept in
`docs/semi-formalized-research-frontiers/drafts/MANIFEST.md` and the local
package records. The rows below are the earlier B2--B11 checkpoint ledger; B7
was superseded by the later historical Up receipt above. The recorded pairs were:

- B2 Frontier Compilations: 17,311 lines / 748,733 bytes /
  `600bab0556c95661c6963438ea3e8e5ed1c691af36d64e1c105435199e605736` →
  275 pages / 2,790,721 bytes /
  `49159c19d59fdd5bd397d3ab70bd024ea5bc7995fb037a532bc1fded9c9ad4fa`.
- B3 Integration and Transform Frontiers: 25,147 / 1,058,819 /
  `b60b232e55af7c021e82dec476823e727ef8398388bda9af0a3334aba4a30be3` →
  377 / 3,292,594 /
  `52b1b7e5cd86cbd8d00cb0d90580ea555b2762d7a638aa52b5ea680dcbca7199`.
- B4 Fabius Information Frontier: 2,138 / 78,310 /
  `57a06279153b6e4c97ea0c084a193867b2f5c60a0163983149f36453eb196c9d` →
  29 / 790,802 /
  `3af03cd4dcc7fb1a502976f47edb56ee7d5c2b8dc9a8da537e79f8382ef885d5`.
- B5 Matrix-Dilated Fabius--Rvachev: 1,997 / 76,958 /
  `5311ff92a6d6d430f3c6e94d61974ffb549a8fe99bb20636a5c47116ad7d9aba` →
  29 / 878,932 /
  `1c7ca0f14f2b456c4bd9692057b63f0941b15ee0810c6f1a3947a2a128a9c76b`.
- B6 Representation Frontiers: 18,637 / 776,458 /
  `dd41bc90b03d1f54d9fae71c116061b0130d505740cb92fe908d6db3c21f3d95` →
  301 / 3,609,120 /
  `4dae6f87e6cc4da953319ba85c18316c23bf6e34a8bdac5680f20255356c4ba7`.
- B7 Up Polynomial Synthesis (historical): 2,324 / 95,757 /
  `15f7c593895ed4a06b7f9d90c72d55078a193cd01f0818cb3b3cfa4f4d585a52` →
  60 / 1,056,613 /
  `0b7fc962bcb4509affc322571100cc4f27252b1ec113ca8116b05c59d23ffd35`.
- B8 Common-Digit Fabius Zonoids: 2,092 / 89,360 /
  `ad6d0bfa137efe0c79cf0ee599845b8708d82ef31f6fc2c3016e80ff14a7675e` →
  36 / 1,171,153 /
  `4169b907f96b46cb75b1aab067e237a431798cfb612bbad11e2a74a38d494cd4`.
- B9 Dyadic Radon Profiles: 2,050 / 74,839 /
  `0ac7695620cb22896bb912598e2e91fd404e70dbd3c5d1e769ee76a6e92578d4` →
  29 / 998,017 /
  `39e76001f71c6628308ccdb8232251538674faee3c9102fa26e4cec00eb276c0`.
- B10 Fabius--Rvachev Carleman Frontiers: 1,934 / 71,224 /
  `49dd91c71df292725e9dfe6de450ac014b47f3c3ba4a5bc8ec02e2d2e76d34e3` →
  24 / 973,424 /
  `13a7f35e23dc5a794d46b431059ce35c0b48c199f1996539b65dee9bc8c16047`.
- B11 Thue--Morse Diagonal Polynomials: 1,763 / 56,530 /
  `eee5751653bb19ec04042f51ded34d74bf8862f5b06b49d47e68ea78bb689c45` →
  24 / 778,595 /
  `8db0c4e0a4fcf682bd3e1311f7d8197ea04dcca56e102236b52494267d99cbbe`.

For provenance, the superseded pre-d8b pairs remain historical receipts:
primary TeX/PDF `938517a92565685ac9f7194b879cfe752ce783f258bde8b7b685aee41aed13dc` /
`bf26d78dd2cc49feb87a85413ef9c04c7a8a3dac4f793cf86e3436f7502cb2a7`
(694,350 / 1,593,577 bytes; 195 PDF pages); walkthrough
`e598aa02d4d10eda8bcfdafe3731f4a663bdcba58407f454485fae6796b41050` /
`5ff79c24fbced37dfaa5eb9c34447d0e7661b2b2bc5a0597687e43f93d7e189a`
(456,855 / 1,219,336 bytes; 145 pages); frontier
`7dd140370a0ac68522364a83a3c6423df93570741eafaef2ee8c1fac17670e2f` /
`9d38ab9d43befd6e26fd06ab9680b4a761365fb9d8a9f0de18489c243bd62d3e`
(808,185 / 1,877,159 bytes; 260 pages); and q-series
`d8f730b8eb6602d4d16112aea77a3e67dfbeadf46bcd28c1cdf3b12450b7d4fb` /
`5d25df07e6df1cd32118ee87e64c1cc54ad32da7c578a182231f98dd9fee9d5c`
(837,715 / 2,494,949 bytes; 395 pages).

`FabiusInverseExactDyadicModulus.lean` contributes two definitions and ten
theorems.  The definitions are `inverseFabiusExactDyadicDenominator` and
`inverseFabiusExactLogarithmicDenominator`.  Its exhaustive theorem surface is
`inverseFabiusExactDyadicDenominator_primrec`,
`inverseFabiusExactDyadicDenominator_pos`,
`inv_inverseFabiusExactDyadicDenominator_le_fabiusAtInverseTwoPow`,
`inverseFabiusExactDyadicDenominator_isLeast`,
`abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_exactDyadicDenominator`,
`exists_fabiusInv_gap_of_lt_exactDyadicDenominator`,
`inverseFabiusExactDyadicDenominator_isLeast_strictModulus`,
`inverseFabiusExactLogarithmicDenominator_primrec`,
`inverseFabiusExactLogarithmicDenominator_of_pos`, and
`abs_fabiusInv_sub_lt_inv_nat_of_lt_exactLogarithmicDenominator`.  The first
denominator is least only for a fixed dyadic output target; the logarithmic
`1/n` conclusion is a witness, not a leastness theorem.  Its value at zero is
the convention `d(0)=1`, with no zero-input modulus conclusion.  The two
named `Primrec` theorems close the recursive-denominator clause without
asserting an input-bit running-time bound.

The retained comb-interpolation synthesis PDF is a validated 160-page A4
historical receipt: the current source includes a post-render update to its
additive-dyadic chapter, so a fresh parity build remains pending.  The rebuilt
Integration-and-Transform master retains a historical 377-page PDF.  The canonical
q-series synthesis is a validated 389-page historical receipt synchronized to
the immediately preceding source checkpoint.  The current source adds the
twelve-declaration terminating q-Chu/reversal closure, so final parity is
again pending.  The retained 210-page primary, 165-page walkthrough, 273-page
canonical frontier, 301-page Representation Frontiers, 41-page New Frontiers,
and 88-page notation-catalogue artifacts likewise predate their current merged
sources.  Their package notices treat those PDFs as historical validation
receipts, not parity claims, until fresh uninterrupted three-pass builds
complete.  The inverse-computability receipt likewise still reflects the
historical 675/8,909 census and requires refresh against the live 1004/12,500
inventory.  The canonical inverse-theory publication retains a 134-page
artifact synchronized at its latest-main source checkpoint; the merged
effective-inversion and superconvergent-synthesis tranches make current parity
pending.

### What the review pass caught

Both waves paired each documenting agent with an independent auditor, and that
was not ceremony.  The recurring defect was never a wrong formula -- it was a
false claim about dependencies: "every coefficient computation below factors
through this" when one does not, "the denominator in every ratio bound here"
when it is the denominator of one, "used by X" when X re-derives it inline.
Prose asserting a dependency is much easier to get wrong than prose asserting a
statement, because the statement is on the next line and the dependency is not.

Two doc comments had silently dropped an ambient `IsFabius F`; one stated its
two interval inclusions in the wrong directions; one said an interval
restriction was necessary when the file proves no converse.

The second wave was told this in advance and instructed to write no "used by"
clause at all unless it had been grepped.  78 verified consumer clauses came
out of that, and the defect rate fell accordingly.

### Doc comments that contradicted their statements

A separate sampling pass read about 190 doc-comment/statement pairs looking
for prose that claims more, or less, than the Lean statement.  The corpus is in
good shape here; three defects were found and fixed.

1. `norm_iteratedDeriv_negativeLaplaceVerticalKernelLogFirst_le` was documented
   as holding "uniformly on every vertical strip center `|theta| <= 1`".  Its
   statement has no such hypothesis: `theta` is an arbitrary real and the
   constant does not mention it.  The prose *understated* the theorem, which
   would have sent a reader looking elsewhere for a bound this lemma already
   gives.

2. and 3. `legendrePolynomial_contDiff` and
   `contDiff_negativeLaplaceVerticalCurve` assert `ContDiff R (top)` with the
   exponent elaborated at `WithTop ℕ∞`.  In this Mathlib that is the *analytic*
   exponent `ω`, not `C^∞`:

   ```text
   Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:118
     scoped[ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)
   Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:120
     scoped[ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)
   ```

   Both were documented as merely "smooth".  The corpus writes `ContDiff ℝ ∞`
   in 66 places and `ContDiff ℝ ⊤` in only these two, so the distinction is
   deliberate everywhere else.

   This distinction is worth policing in this corpus in particular.  Its
   central regularity result is that the Fabius function is `C^∞` everywhere
   and analytic exactly off `[0,1]`; a doc comment that says "smooth" over an
   `ω` statement is the one confusion the library exists to prevent.

## Ongoing documentation maintenance

1. Any new file: header and doc comments at the time of writing.  The ratchet
   gate makes this cheap to enforce.
2. Run the audit after each source tranche and update the checked baseline only
   after reviewing the reported declarations.
3. Keep comments on declarations cited by `PAPER_COVERAGE.md` synchronized
   with their exact proved strength, since those are the ones an outside reader
   reaches first.
4. Review long interior estimate chains when they change, ideally while their
   local proof structure is still fresh.

Adding a doc comment cannot change elaboration, so this work needs no build
slot.  On a machine where a full rebuild costs the better part of a day, that
makes it unusually good value.
