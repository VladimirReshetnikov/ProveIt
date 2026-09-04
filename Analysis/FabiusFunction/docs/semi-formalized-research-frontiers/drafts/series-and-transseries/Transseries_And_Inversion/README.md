# Transseries: the polynomial–logarithmic calculus and its inversions

**Single consolidated volume for the whole `series-and-transseries` group.**
`transseries_and_inversion.tex` is the canonical editable source. The retained
695-page PDF was built on 4 September 2026 before the current Lean-crosswalk
edits; it is historical and unrebuilt, and no current source/render parity is
claimed.

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

The live corpus census is 943 modules and 11,787 explicit public declarations,
with zero missing declaration comments and zero missing module headers. The
nine directly relevant modules contain 72 explicit public commands; two named
`to_additive` declarations bring this inventory to 74 named API entries.
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
- `TransseriesWellBased.lean` (five written theorems):
  `dickson_isPWO`, `dickson_antichain_finite`, `dickson_isPWO_pi`,
  `neumann_isPWO`, and `neumann_finite_factorizations`; `to_additive`
  additionally generates `neumann_add_isPWO` and
  `neumann_finite_decompositions`.
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
- `TransseriesDifferentialBlock.lean` (five theorems):
  `derivation_pow_t`, `derivation_block`, `exists_block_primitive`,
  `derivation_block_zero`, and `exists_block_primitive_resonant`.
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

The exact status map is deliberately narrower than the inventory:

- Exact: `q0:def:scale`, `q0:eq:scale`, `q0:def:poincare`,
  `q0:eq:poincare`, `q0:eq:coefficients`, `q0:prop:uniqueness`,
  `q0:lem:dickson`, the analytic content of
  `plt:lem:mot-dominance`, all three unit-series Bell results
  `p0:lem:bell-conversion`, `p0:lem:power-log`, and
  `p0:cor:exp-log-jets`, and `p6:prop:quadratic-core-catalan`.
- Partial: `q0:lem:neumann` until the order-dual wrapper is exposed;
  `q0:prop:height` beyond its two exact displayed estimates;
  `plt:def:mot-scale` beyond the ordered-sequence version;
  `plt:lem:mot-block-antiderivative` and `plt:prop:dif-block` beyond natural
  powers and the polynomial coefficient operator; and
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
for this tranche. The current TeX has 3,111 distinct labels. The retained
historical PDF has 695 A4 pages and predates the present source.
