# Transseries: the polynomial–logarithmic calculus and its inversions

**Single consolidated volume for the whole `series-and-transseries` group.**
`transseries_and_inversion.tex` is the canonical editable source. The retained
702-page PDF was built on 4 September 2026 from the 55,005-line,
3,111-label publication checkpoint. The current 55,319-line source has 3,118
distinct labels and includes later Lean-crosswalk edits; the retained artifact
is therefore historical and no current source/render parity is claimed.

## Status

Complete. All five source groups are merged, and all five source
directories were residue-audited and deleted on 4 September 2026. “Complete”
here describes the editorial consolidation, not full machine formalization.

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

The live corpus census is 952 modules and 11,884 explicit public declarations,
with zero missing declaration comments and zero missing module headers. The
eighteen directly relevant modules contain 169 explicit public commands; two
named `to_additive` declarations bring this inventory to 171 named API entries.
Automatically generated structure projections are outside both tallies.

- `TransseriesScale.lean` (one structure, one definition, three theorems):
  `IsAsymptoticScale`, `IsPoincareExpansion`,
  `IsPoincareExpansion.isLittleO_succ_remainder`,
  `IsPoincareExpansion.tendsto_coeff`, and
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
- `TransseriesDifferentialBlock.lean` (nine theorems):
  `derivation_pow_t`, `derivation_block`, `exists_block_primitive`,
  `derivation_block_zero`, `exists_block_primitive_resonant`,
  `derivation_val_inv`, `derivation_pow_inv`, `derivation_zpow_t`, and
  `derivation_block_zpow`.
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
- `TransseriesFlat.lean` (four definitions, sixteen theorems): `IsFlat`,
  `flatSubmodule`, `AbsorbsScale`, `powScale`, `isFlat_zero`, `IsFlat.add`,
  `IsFlat.neg`, `IsFlat.sub`, `IsFlat.const_smul`,
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
- `RemainderTransport.lean` (three theorems):
  `lipschitzOn_of_abs_deriv_le`, `transport_bound_mul`, and
  `transport_bound`.
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

The exact status map is deliberately narrower than the inventory:

- Exact: `q0:def:scale`, `q0:eq:scale`, `q0:def:poincare`,
  `q0:eq:poincare`, `q0:eq:coefficients`, `q0:prop:uniqueness`,
  `q0:def:flat`, `q0:prop:invisible`, `q0:lem:dickson`, `q0:lem:neumann`
  through its literal `OrderDual` wrappers (the printed total order is a
  specialization), the analytic content of `plt:lem:mot-dominance`,
  `plt:prop:mot-omega-basic` over the reals only, and the displayed equations
  `plt:eq:mot-block-derivative` and `plt:eq:dif-block` in the abstract unit
  model, `plt:lem:bell-normalizations`, all three
  unit-series Bell results
  `p0:lem:bell-conversion`, `p0:lem:power-log`, and
  `p0:cor:exp-log-jets`, and `p6:prop:quadratic-core-catalan`.
- Partial: `q0:prop:height` beyond its two exact displayed estimates;
  `plt:def:mot-scale` beyond the ordered-sequence version;
  `plt:lem:mot-harmonic` beyond its leading Stolz limit;
  the compound `plt:lem:mot-block-antiderivative` and `plt:prop:dif-block`
  beyond their exact integer equations and polynomial coefficient operator,
  since the concrete Laurent ambient, faithful evaluation, ambient uniqueness,
  and general-exponent apparatus are absent;
  `p0:thm:lambert-core` beyond its real algebra and branch rules;
  `p0:thm:staircase` beyond its order-theoretic clauses;
  `p0:thm:remainder-transport` beyond the displacement bound;
  `p6:lem:core` beyond the real `r = 1` case;
  `p8:cor:nearest-integer` beyond integer arguments; and
  `p6:lem:quadratic-core` beyond its verified coefficient recurrence.
- Absent: the assembled two-generator Laurent-series calculus, composition
  and reversion at infinity, and `p6:thm:deepest-pole`.

The Bell statements are formal power-series identities: they make no analytic
convergence or branch claim. The weighted-partition formula is most generally
stated with rational scalar multiplication over a commutative rational
algebra; literal division is a characteristic-zero-field specialization.

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
  proposition is a corollary of it and not conversely;
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

What the inversion apparatus genuinely adds over the calculus is the
exponential–power model and its axiomatized dominant core, the monomial
α-reduction, perturbed inversion around an exactly invertible core, the
ordinary Bell family, the two-sided backward-error certificate, and — with no
analogue anywhere in the calculus — the theory of inverting a **sequence**:
three distinct inverse objects, the staircase theorem, and the separation
condition. The calculus is a theory of functions on a scale; that last group
is about the passage from a function to a sequence.

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

## Build

The former assembler cannot be rerun; the `.tex` header identifies the
consolidated file as the canonical source and it is now edited in place. A
future publication build would use three `pdflatex` passes, but none was run
for this tranche. The current TeX has 55,319 lines and 3,118 distinct labels.
The retained historical PDF has 702 A4 pages and was built from the preceding
55,005-line, 3,111-label source checkpoint; no current source/render parity is
claimed.
