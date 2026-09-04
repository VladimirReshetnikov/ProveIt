# Transseries: the polynomial–logarithmic calculus and its inversions

**Single consolidated volume for the whole `series-and-transseries` group.**
`transseries_and_inversion.tex` is the canonical editable source. The local
704-page and incoming 711-page A4 PDFs are historical publication checkpoints.
The local 704-page receipt remains recorded below, including its disclosed
layout warnings. The incoming branch later reached 55,985 lines and 3,125
distinct labels; the merged canonical source includes still later editorial
and Lean-crosswalk changes. Neither artifact is therefore current. The accepted
merged-source render is recorded in the [merge-28de4e51 receipt
register](../../MANIFEST.md#merge-28de4e51-publication-receipts).

## Status

Editorial consolidation is complete. All five source groups are merged, and all
five source directories were residue-audited and deleted on 4 September 2026.
“Complete” describes the editorial consolidation, not full machine
formalization. Current publication parity is recorded in the receipt register
linked above.

| Source group | Lines | Absorbed as |
| --- | --- | --- |
| `transseries-tutorials/` (4 articles) | 26,099 | Part I, Orientation |
| `polynomial-logarithmic-transseries/` (1 volume) | 36,033 | Parts II–IX, the calculus |
| `special-function-inversion/` (1 volume) | 16,771 | Parts X–XIV |
| `lambert-inverse-transseries/` (3 articles) | 5,209 | Part XI, `x + W(x)` |
| `sequence-transseries/` (5 articles) | 9,743 | Part XIV, Bell and Fubini |

The provenance appendix lists all forty-two sources with the part that
absorbed each; the repair appendix lists every correction made.

## Lean formalization inventory

The live corpus census is 988 modules and 12,257 explicit public declarations,
with zero missing declaration comments and zero missing module headers. The
thirty-five directly relevant modules contain 304 explicit public commands; two
named `to_additive` declarations bring this inventory to 306 named API entries.
The 979/12,142 census is the preceding historical checkpoint.
Automatically generated structure projections are outside both tallies.

- `TransseriesScale.lean` (one structure, two definitions, six theorems):
  `IsAsymptoticScale`, `IsPoincareExpansion`, `poincarePartialSum`,
  `poincarePartialSum_zero`, `poincarePartialSum_succ`,
  `IsPoincareExpansion.isLittleO_succ_remainder`,
  `IsPoincareExpansion.tendsto_coeff`,
  `IsPoincareExpansion.tendsto_coeff_div`, and
  `IsPoincareExpansion.coeff_unique`.
- `TransseriesScaleDominance.lean` (one definition, seven theorems):
  `plMonomial`, `tendsto_plMonomial_atTop_zero`,
  `plMonomial_div_eventuallyEq`,
  `tendsto_plMonomial_div_atTop_zero`,
  `tendsto_plMonomial_div_atTop_one`, `plMonomial_pos`,
  `tendsto_plMonomial_div_atTop`, and
  `plMonomial_generators_dominance`.
- `TransseriesPolyLogScale.lean` (four theorems):
  `isLittleO_plMonomial`, `isAsymptoticScale_plMonomial`,
  `isAsymptoticScale_plMonomial_pow`, and
  `isAsymptoticScale_plMonomial_log`.
- `TransseriesWellBased.lean` (seven written theorems):
  `dickson_isPWO`, `dickson_antichain_finite`, `dickson_isPWO_pi`,
  `neumann_isPWO`, `neumann_finite_factorizations`,
  `neumann_isPWO_orderDual`, and
  `neumann_finite_factorizations_orderDual`; `to_additive` additionally
  generates `neumann_add_isPWO` and `neumann_finite_decompositions`.
- `TransseriesHeight.lean` (three theorems):
  `isLittleO_log_pow_rpow`, `isLittleO_log_pow_id`, and
  `isLittleO_pow_mul_log_pow_exp`.
- `TransseriesBlockAntiderivative.lean` (three definitions, twelve
  theorems): `blockOperator`, `blockAntiderivative`,
  `resonantAntiderivative`, `sum_sub_sum_shift`, `blockOperator_zero`,
  `blockOperator_sub`, `blockOperator_blockAntiderivative`,
  `blockOperator_surjective`, `natDegree_C_mul_of_ne_zero`,
  `natDegree_blockOperator`, `blockOperator_injective`,
  `blockOperator_bijective`, `derivative_resonantAntiderivative`,
  `derivative_surjective`, and `natDegree_resonantAntiderivative`.
- `TransseriesDifferentialBlock.lean` (one definition, twenty theorems):
  `derivation_pow_t`, `derivation_block`, `successiveBlockOperator`,
  `successiveBlockOperator_zero`, `successiveBlockOperator_succ_last`,
  `blockOperator_comm`, `blockOperator_successiveBlockOperator`,
  `successiveBlockOperator_add`, `successiveBlockOperator_succ_first`,
  `derivation_iterate_block`, `derivation_zpow_block`,
  `exists_zpow_block_primitive`, `existsUnique_zpow_block_primitive`,
  `exists_block_primitive`,
  `derivation_block_zero`, `exists_block_primitive_resonant`,
  `derivation_val_inv`, `derivation_pow_inv`, `derivation_zpow_t`,
  `derivation_block_zpow`, and `derivation_iterate_block_zpow`.
- `UnitSeriesBellCoefficients.lean` (sixteen theorems):
  `ordPartialBell_eq_factorialRatio_partialBell`,
  `factorial_mul_ordPartialBell_eq_factorial_mul_partialBell`,
  `coeff_fallingSeries_subst_eq_sum_ordPartialBell`,
  `coeff_fallingSeries_subst_eq_sum_ordPartialBell_of_pos`,
  `coeff_fallingSeries_subst_eq_sum_partialBell`,
  `coeff_negBinomSeries_subst_eq_sum_ordPartialBell`,
  `coeff_negBinomSeries_subst_eq_sum_ordPartialBell_of_pos`,
  `coeff_logOf_eq_sum_ordPartialBell`,
  `egfA_factorialDenormalize_coeff_eq`,
  `bellWeightSeries_factorialDenormalize_coeff_eq`,
  `coeff_logOf_eq_sum_partialBell`,
  `coeff_exp_subst_eq_completeBell`,
  `coeff_exp_subst_eq_partitionExpSum`,
  `coeff_exp_subst_eq_sum_weightedPartitions`,
  `coeff_exp_subst_eq_sum_div_weightedPartitions`, and
  `coeff_exp_subst_recurrence`.
- `QuadraticCoreCatalan.lean` (three definitions, eight theorems):
  `quadHalf`, `halfBinom`, `quadCoef`, `catalan_two_step`,
  `quadHalf_zero`, `quadHalf_antidiagonal`, `halfBinom_step`,
  `quadHalf_rat`, `quadCoef_rat`, `quadCoef_zero`, and `quadCoef_rec`.
- `TransseriesFlat.lean` (four definitions, twenty-two theorems): `IsFlat`,
  `flatSubmodule`, `AbsorbsScale`, `powScale`, `isFlat_zero`, `IsFlat.add`,
  `IsFlat.neg`, `IsFlat.sub`, `IsFlat.const_smul`,
  `isFlat_exp_neg_rpow_atTop`, `IsPoincareExpansion.add_flat`,
  `IsPoincareExpansion.sub_same_coeff_isFlat`,
  `IsPoincareExpansion.iff_sub_isFlat`,
  `IsFlat.smul_of_scale_absorption`, `IsFlat.smul_of_isBigO_inv_pow`,
  `mem_flatSubmodule_iff`, `IsFlat.mul_absorbsScale`,
  `absorbsScale_const`, `IsPoincareExpansion.add_isFlat`,
  `isFlat_sub_of_isPoincareExpansion`,
  `isPoincareExpansion_iff_isFlat_sub`,
  `isPoincareExpansion_zero_iff`, `powScale_eq_rpow`,
  `absorbsScale_of_isBigO_pow`, `isFlat_exp_neg`, and
  `isPoincareExpansion_add_exp_neg`.
- `WrightOmega.lean` (one definition, thirteen theorems): `wrightOmega`,
  `analyticAt_wrightOmega`, `wrightOmega_pos`, `wrightOmega_add_log`,
  `principalLambertW_eq_wrightOmega_log`, `wrightOmega_leftInverse`,
  `wrightOmega_strictMono`, `wrightOmega_one`, `one_le_wrightOmega`,
  `wrightOmega_le_self`, `sub_log_le_wrightOmega`, `wrightOmega_envelope`,
  `add_one_div_two_le_wrightOmega`, and `tendsto_wrightOmega_atTop`.
- `TransseriesHarmonicIncrement.lean` (two theorems):
  `tendsto_div_atTop_of_tendsto_sub` and
  `tendsto_div_atTop_of_harmonic_increment`.
- `OrdinaryPartialBell.lean` (two definitions, four theorems):
  `ordinarySeries`, `ordinaryPartialBell`, `ordinaryPartialBell_pow`,
  `bellWeightSeries_eq_ordinarySeries`,
  `factorial_mul_ordinaryPartialBell`, and
  `ordinaryPartialBell_eq_zero_of_lt`.
- `LinLogCoreInversion.lean` (four definitions, eighteen theorems):
  `linLogCoreArg`, `linLogCoreRoot`, `linLogCoreThreshold`,
  `linLogCoreRootLower`, `linLogCore_eq_iff`,
  `principalLambertW_linLogCoreArg_pos`, `linLogCoreRoot_pos`,
  `linLogCore_linLogCoreRoot`, `strictMonoOn_linLogCore`,
  `linLogCoreRoot_unique`, `hasDerivAt_linLogCore`,
  `linLogCore_slope_eq`, `linLogCore_critical`,
  `linLogCoreArg_mem_Ioo_iff`, `principalLambertW_linLogCoreArg_neg`,
  `linLogCoreRoot_pos_of_neg`, `linLogCoreRootLower_pos`,
  `linLogCore_linLogCoreRoot_of_neg`, `linLogCore_linLogCoreRootLower`,
  `linLogCoreRoot_lt_critical`, `critical_lt_linLogCoreRootLower`, and
  `linLogCoreRoot_ne_linLogCoreRootLower`.
- `PowerLogCoreInversion.lean` (three definitions, six theorems):
  `powerLogCore`, `powerLogCoreArg`, `powerLogCoreRoot`,
  `powerLogCore_exp`, `log_powerLogCoreRoot_sub`,
  `powerLogCore_of_lambert`, `powerLogCore_powerLogCoreRoot`,
  `hasDerivAt_powerLogCore`, and `hasDerivAt_powerLogCore_root`.
- `RemainderTransport.lean` (four theorems):
  `lipschitzOn_of_abs_deriv_le`, `transport_bound_mul`, `transport_first_order`,
  and `transport_bound`.
- `StaircaseInversion.lean` (seven theorems): `isLeast_ceil`,
  `staircase_ceil`, `staircase_separation`, `staircase_separation_fails`,
  `staircase_round`, `isLeast_residue_class`, and
  `exists_half_error_of_jump`.
- `DerangementNearestInteger.lean` (one definition, seven theorems):
  `subfactorialDefect`, `subfactorialDefect_zero`,
  `subfactorialDefect_succ`, `subfactorialDefect_pos`,
  `subfactorialDefect_lt`, `numDerangements_sub_eq`,
  `abs_numDerangements_sub_lt_half`, and
  `round_factorial_mul_exp_neg_one`.

At the earlier focused checkpoint, fourteen incoming leaves added 95 focused
declarations:
`BackwardErrorExistence.lean` (7), `BellLeibnizTower.lean` (5),
`CayleyKernel.lean` (10), `CayleyLocalCoordinate.lean` (7),
`CayleyTreeFunction.lean` (7), `DivisorTransform.lean` (9),
`ExpSeriesRecurrence.lean` (4), `LambertCorrectionEquation.lean` (8),
`LambertShiftConcavity.lean` (5), `LeastTermIndex.lean` (7),
`TouchardEulerOperator.lean` (9), `TransseriesBlockClasses.lean` (3),
`TransseriesDifferentialClosure.lean` (12), and
`TransseriesMonomialUniqueness.lean` (2). Their declaration-level boundaries
are recorded beside the corresponding results in the canonical TeX. The
fifteenth incoming leaf, `NewtonInterpolation.lean` (22), belongs to another
focused package. Three later focused leaves add
`StirlingSeriesCoefficients.lean` (15), `WrightOmegaTwoOrders.lean` (8), and
`UnitSeriesPowerRecurrence.lean` (3). `NewtonInterpolation.lean` and the eleven
new `AppellSequence.lean` declarations are included only in the global corpus
census above.

The final focused addition is the ten-theorem
`TransseriesWrightOmegaTerms.lean` leaf:
`plMonomial_one_zero_eventuallyEq`, `plMonomial_zero_one_eventuallyEq`,
`plMonomial_neg_one_one_eventuallyEq`, `exponents_of_wrightOmega`,
`exponents_of_wrightOmega_sub`, `exponents_of_wrightOmega_residual`,
`not_pure_of_wrightOmega_three_terms`,
`not_isEquivalent_pure_power_wrightOmega_sub`,
`tendsto_wrightOmega_div_plMonomial_zero_atTop`, and
`isLittleO_wrightOmega_residual_plMonomial_zero`.  The two added theorems in
`TransseriesMonomialUniqueness.lean` are
`tendsto_const_mul_plMonomial_div_one_iff` and
`isEquivalent_const_mul_plMonomial_iff`; the two earlier compatibility
wrappers remain.  These twelve declarations account exactly for the change
from the historical 35/304/306 focused inventory to 36/316/318.

The exact status map is deliberately narrower than the inventory:

- Exact: `q0:def:scale`, `q0:eq:scale`, `q0:def:poincare`,
  `q0:eq:poincare`, `q0:eq:coefficients`, `q0:prop:uniqueness`,
  `q0:def:flat`, `q0:prop:invisible`, `q0:lem:dickson`, `q0:lem:neumann`
  through its literal `OrderDual` wrappers (the printed total order is a
  specialization), the analytic content of `plt:lem:mot-dominance`,
  `plt:prop:mot-blocks`, `plt:prop:mot-omega-basic` over the reals only,
  the unique first three Wright-omega monomial terms, and the real-`atTop`
  statements `plt:cor:mot-both-generators-needed` and
  `plt:prop:mot-one-generator-fails`,
  `plt:lem:tay-bell-recurrence`, and the displayed equations
  `plt:eq:mot-block-derivative` and `plt:eq:dif-block` in the abstract unit
  model, `plt:lem:bell-normalizations`, all three
  unit-series Bell results
  `p0:lem:bell-conversion`, `p0:lem:power-log`, and
  `p0:cor:exp-log-jets`, and `p6:prop:quadratic-core-catalan`.
- Partial: `q0:prop:height` beyond its two exact displayed estimates;
  `plt:def:mot-scale` beyond the ordered-sequence version;
  `plt:lem:mot-harmonic` beyond its leading Stolz limit;
  `plt:prop:mot-two-orders` beyond its exact concluding equivalences and at
  its four-term quantitative expansion; the abstract construction of a full
  transseries scale beyond the proved monomial set consequences;
  `plt:thm:mot-smallest-differential-algebra` beyond its exact
  abstract minimality statements and integer block law, since the concrete
  germ-model growth and algebraic-independence clauses remain absent;
  the compound `plt:lem:mot-block-antiderivative` and `plt:prop:dif-block`
  beyond their exact integer equations, polynomial coefficient operator, and
  conditional nonresonant primitive API, since the concrete Laurent ambient
  and remaining faithful-evaluation/uniqueness links are absent;
  `p0:thm:lambert-core` beyond its real algebra and branch rules;
  `p0:thm:staircase` beyond its order-theoretic clauses;
  `p0:thm:remainder-transport` beyond its exact displacement and explicit-error
  clauses, since the closing asymptotic clause remains absent;
  `p6:lem:core` beyond the real `r = 1` case;
  `p8:cor:nearest-integer` beyond integer arguments; and
  `p6:lem:quadratic-core` beyond its verified coefficient recurrence.
- Absent: the assembled two-generator Laurent-series calculus, composition
  and reversion at infinity, and `p6:thm:deepest-pole`.

The Bell statements are formal power-series identities: they make no analytic
convergence or branch claim. The weighted-partition formula is most generally
stated with rational scalar multiplication over a commutative rational
algebra; literal division is a characteristic-zero-field specialization.
`UnitSeriesPowerRecurrence.lean` adds the generic commutative-ring recurrence
from `F G' = β F' G` and its unit-series falling-factorial specialization over
a commutative rational algebra. This makes the coefficient-calculus arbitrary-
power recurrence exact, but introduces no analytic power or branch choice.

## How the two apparatuses relate

The `series-and-transseries` README recorded, as an explicitly open question,
whether the polynomial–logarithmic calculus and the inversion calculi of the
special-function articles coincide. The concordance chapter answers it, pair
by pair, and the answer is **less overlap than a title-level comparison
suggests**.

An earlier stage of this merge, working from title matching alone, recorded
that the calculus "already contains" Lagrange–Bürmann at infinity and at a
finite point, residual-to-error transfer, both Bell families,
affine-logarithmic reversion and the pure Lambert block, and concluded the
inversion apparatus was largely redundant. Reading the statements shows that
overstated it. The accurate tally, of six apparent overlaps:

* **one genuine duplicate** — the exponential partial Bell polynomials are the
  same definition in two notations (proved in the concordance);
* **one strengthening in the inversion apparatus's favour** — the calculus has
  the one-sided mean-value bound, while the inversion apparatus has the
  two-sided bracket *and* the root-existence certificate, so the calculus's
  proposition is a corollary of it and not conversely.  The certificate is now
  machine-checked as `Fabius.exists_eq_in_residual_interval`; unlike the two
  error inequalities, it assumes no pre-existing root or right inverse;
* **one item with no counterpart** — the calculus defines only the exponential
  Bell family; the ordinary family is new;
* **three pairs that are different theorems about the same subject** —
  Lagrange–Bürmann in near-identity *operator* form against classical
  *coefficient* form; reversion of `X + aL` by Lambert polynomials against the
  closed-form pure Lambert block; leading-order slope transport against a
  bound with an explicit second-order error.

Shared vocabulary is a weak signal: two results both called
"Lagrange–Bürmann" turned out to be different theorems, and a mechanical
concordance reports them as the same. Only reading the statements settles it.

The current source adds a scoped Lean crosswalk rather than a title-based one.
It identifies exact counterparts for the abstract asymptotic-scale and
Poincaré-expansion core, flatness and invisible functions, the relevant
Hahn-series foundations, polynomial--logarithmic height estimates, Wright omega
apart from real analyticity, differential-block integration, staircase
inversion, and residual/error transport. Each note records its boundary; the
crosswalk does not promote the volume's remaining human proofs or frontier
claims wholesale.

What the inversion apparatus genuinely adds over the calculus is the
exponential–power model and its axiomatized dominant core, the monomial
α-reduction, perturbed inversion around an exactly invertible core, the
ordinary Bell family, the two-sided backward-error certificate, and — with no
analogue anywhere in the calculus — the theory of inverting a **sequence**:
three distinct inverse objects, the staircase theorem, and the separation
condition. The calculus is a theory of functions on a scale; that last group
is about the passage from a function to a sequence.

## Lean crosswalk

The current integrated inventory is 988 modules and 12,257 public declarations,
with no documentation gaps. The preceding 979/12,142 inventory is a historical
checkpoint. `TransseriesFlat` now has 4 definitions
and 22 theorems, preserving the general vector-valued API together with the
scalar submodule, absorption, and power-scale interfaces. The integer block
interfaces and the incoming inverse-power derivative lemmas together make
`TransseriesDifferentialBlock` a 12-theorem module.
The source records status claim by claim. Exact counterparts now cover the
sequence-indexed asymptotic-scale/Poincaré definitions and uniqueness,
flatness and the corrected invisible-function proposition, Dickson and Neumann
(with `OrderDual` matching the manuscript's well-based orientation), the
displayed power–log ratio limits and chosen decreasing
sequence scales, the unique first three Wright-omega monomial terms and both
real one-generator failures, the unit-series Bell coefficient formulas, and the quadratic
Catalan identity. The full unordered power–log scale lemma, the all-integer
Laurent block-antiderivative lemma, and the complete quadratic-core lemma are
Partial at the boundaries stated in the source. No status promotion should be
inferred for the surrounding transseries constructions.

The incoming `BellLeibnizTower` and `OrdinaryPartialBell` modules supply the
abstract Faà di Bruno formula and the ordinary/exponential normalization
bridge. `TouchardEulerOperator` supplies the Touchard definition, coefficient
identities, and displayed Euler-operator equation. The backward-error,
transfer, and Lambert-certificate
claims depend on assembling their named existence and comparison theorems.
The broader Wright-omega, differential-closure, harmonic-increment, Cayley,
derangement, Lambert-correction and bracket, core-inversion,
remainder-transport, and staircase claims remain Partial where their source
clauses exceed the exposed APIs. `LeastTermIndex` supplies neighboring
ratio and unimodality lemmas; it does not prove the full optimal-truncation
claim.
## Structure

Part I orients: what a transseries is, why a scale is needed, why divergence is not failure, and the algebra of monomials — replacing four parallel expository introductions.

Parts II–IX are the calculus: the polynomial–logarithmic scale; arithmetic
and differential calculus; composition; series reversal at infinity; Wright
omega, the Lambert polynomials and Lambert `W`; from formal transseries to
analytic asymptotics; algorithms, certificates and diagnostics; extensions.

The remaining parts apply it: the apparatus for inverting a rapidly growing
function; four combinatorial sequences (rooted trees A000081, the double
factorial, the partition numbers A000041, the swing factorial A056040); four
special functions (Γ and Barnes `G`, the hyperfactorial `K`, the subfactorial,
a real-argument Fibonacci function); the reversal of `x + W(x)` in depth; the Bell numbers by a Lambert saddle and the Fubini numbers by an exact pole lattice; and a synthesis.

## Artifact status

The former assembler cannot be rerun; the `.tex` header identifies the
consolidated file as the canonical source and it is now edited in place. The
local 704-page receipt was root
`55015L/2732554B/545d4b5ead18831e37a4df0ab7fb6b74a40e1e598144dc7057e8c62aaaa46799`,
two-file closure
`55299L/2744389B/499a045ab45fdea7849c888bc8903db0866a2d4ca27eca3db6f62a9db282af30`,
passes `677/704/704`, PDF
`704pp/5119857B/45a84240f21e501a77571bc860e5bc4693898e27056c82119cf9e4813ddf31a4`,
and log
`4099L/160665B/c7eac59d5bfb747c1f83c2f8b277e8a667049dc1b8e3d04fd9b3c7f6dd637396`;
it retained 114 overfull boxes and 11 duplicate Hyperref targets. The incoming
711-page checkpoint is later but also predates the merged source-only crosswalk
overlay. Both receipts are historical. A future publication build requires
three `pdflatex` passes; no current source/render parity is asserted.
