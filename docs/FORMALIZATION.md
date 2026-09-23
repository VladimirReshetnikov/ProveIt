# Formalization coverage and dependency ledger

The objective is to formalize **all mathematical results in the repository's
surreal and surcomplex documents**, including their hypotheses and size
restrictions. This ledger starts from the main reports; it is not a reduction
of that objective to the statements easiest to count or prove.

The implementation plan is the foundations report,
[`foundations/article.tex`](foundations-and-computation/foundations/article.tex),
especially `found:sec:architecture`, `found:sub:layers`,
`found:sub:contracts`, and `found:sub:milestones`. The report describes a
proposal, not an existing implementation. The preserved Lean sketches under
its `code/` directory are source artifacts; their presence does not establish
that the current Lean target compiles or imports them.

## Scope and how to read this ledger

The canonical inventory below identifies **44 main texts** with **2030**
standard result environments. Counts cover
literal `theorem`, `lemma`, `proposition`, and `corollary` environments;
examples, equations, prose assertions and companion proofs contain further
claims. Counts are a navigation aid, **not a completeness certificate**.
The foundations report has 31 numbered result/example/principle environments,
including seven examples and one design principle; the narrower inventory
counts its 23 standard results.

The inventory and statement index include the ten reports and six report
expansions integrated through `66dd6bc`, plus batch 19: four new reports and
further expansions of four existing reports, integrated from `7657737`.
The four further report drafts placed in `5fe7f8d` are also indexed in their
current form; their assembly and review remain pending. Inclusion supplies
navigation, not mathematical review or formalization. The implementation
table retains the precise scope of the newly mapped Lean statements.

Before archive retirement in `e5791a8`, the tree contained 63 source
manuscripts with 1582 literal standard result environments. Those are historical
counts, not additional independent results: merged reports overlap them and
sometimes change scope or correct a statement. The originals remain available
in Git history, for example `git show 608dd23:docs/<report>/sources/<file>`.
The computable-surreals report adds three separately identified source packages;
its [provenance manifest](foundations-and-computation/computable-surreals/data/provenance-manifest.json)
records archive identities and hashes, but those originals were never tracked here.
A complete coverage audit must still map every source claim to an equivalent
main-report statement, a separate obligation, or a documented correction.
The reports' reconciliation records, verification code and recorded outputs
support that audit; no equivalence is presumed from archive removal.

The unnumbered companion texts
[`short-proof.tex`](surreal/hahn-evaluation-at-omega/short-proof.tex) and
[`short_proof.tex`](surreal/genetic-gaps-and-primitives/short_proof.tex)
likewise need claim-by-claim reconciliation. Existing program checks and LaTeX
build records do not prove the mathematical statements in Lean.

Statuses are deliberately strict:

- **Pending**: no checked Lean theorem has yet been mapped to the entire source
  statement, with all its hypotheses and conclusions.
- **Prerequisites proved**: some reusable algebra or an abstract conditional
  theorem is checked; the full source statement remains pending.
- **Proved**: an imported, compiled Lean declaration matches the full statement,
  and its axiom dependencies have been inspected. A conditional theorem counts
  only for its stated hypotheses; instantiation at surreal numbers needs its
  own checked construction or bridge.
- **Needs correction**: a stated claim is false or underspecified as written;
  record the counterexample or missing hypothesis before formalizing a corrected
  statement. Never conceal this state with `axiom`, `sorry`, or an impossible
  typeclass assumption.

The main-report index is **pending unless mapped below**, with the
implementation table recording progress at the precise clause level.
A checked abstract theorem is not a construction of the surreal ordered field
or a normal-form bridge.

Reuse the pinned Mathlib library before rebuilding its constructions: the
initial algebra uses `QuadraticAlgebra`, `IsRealClosed`, `IsAlgClosed`, and
existing polynomial factorization/extension results. Repository declarations
should expose the manuscript correspondence and prove the genuinely missing
bridges rather than duplicate the library.

The independently maintained `combinatorial-games` library supplies the
numeric-game quotient and its proved ordered field. A
[vendored dependency](../vendor/combinatorial-games/README.md) records the
exact upstream revision, 28-module import closure, Apache license and three
proof-script compatibility changes for the pinned Lean/Mathlib version.
No mathematical statement or arithmetic definition is changed. Its field
construction is included in the transitive axiom audit. An explicit order
isomorphism with the existing sign carrier now preserves every small cut
and its already constructed additive structure. Transporting multiplication
and inverse gives a proved ordered field on that same sign carrier.
Finite normal forms now embed faithfully in the actual sign field, preserving
valuation, leading coefficient and positivity. Canonical cut evaluation of
arbitrary small formal forms now gives an ordered field isomorphism with
inverse extraction, exact real monomials, and finite-evaluation agreement.
Small divisible workspaces now contain every small formal family, and their
odd-degree roots prove real closedness of the formal and actual sign fields.
Small strong real and complex sums, their algebraic operations, actual
valuation/leading data/standard part, and exponent-workspace coherence are
proved below. Actual univariate formal evaluation and its composition law
are also constructed, including finite-variable evaluation. Recentered ordinary
complex analytic Taylor lifting preserves sums and products. Fine derivatives
are proved for polynomials, formal evaluation at zero, and these Taylor lifts
at ordinary centers. General re-expansion/differentiation, multivariable analytic
lifting, analytic composition, and universe coherence remain separate obligations.

## Implementation mappings

The mapped modules pass `lake build`, including the default `SurrealAudit`
target. The audit checks every imported `Surreal` and `SurrealHahnSeries` declaration and rejects any
transitive axiom beyond `propext`, `Quot.sound`, and `Classical.choice`. All ten
size-obstruction theorems have no axiom dependencies. This establishes the
listed Lean statements, not the outstanding surreal interpretation. Every
main-report statement not fully covered below remains pending, including
remaining clauses of a partially mapped statement.

| Source obligation | Lean declarations | Scope of current implementation |
|---|---|---|
| Fine derivative definition and uniqueness in `found:eq:derivative`, `found:sub:derivative`; elementary calculus prerequisites | `Surreal.FineHasDerivAt`, `unique`, `congr_of_eventuallyEq`, `const`, `id`, `add`, `neg`, `sub`, `continuousAt`, `mul`, `pow`, `polynomial` in [Algebra/FineDerivative.lean](../Surreal/Algebra/FineDerivative.lean); both fields' `fineHasDerivAt_iff`, `fineHasDerivAt_unique`, `fineHasDerivAt_of_quadratic_remainder` in [Surcomplex/FineDerivative.lean](../Surreal/Surcomplex/FineDerivative.lean) | The difference quotient tends through the full punctured neighborhood. On actual surreals and surcomplex numbers this is exactly the ε–δ definition with every positive surreal tolerance and radius. Derivatives are unique, local equality preserves them, they imply continuity, and native polynomials differentiate to their formal derivative. A uniformly bounded local quadratic remainder gives the derivative. **Proved** without a real-valued norm, Archimedean assumption or small-index limit. General chain/inverse rules remain separate. Build and axiom audit pass. |
| Zero-derivative/nonconstant counterexample in `found:rem:fourtypes` | `fineHasDerivAt_indicator_of_isClopen`, `infinitesimalIndicator`, `_zero`, `_one`, `_add`, `fineHasDerivAt_infinitesimalIndicator`, `infinitesimalIndicator_not_constant` in [LocallyConstantDerivative.lean](../Surreal/Surcomplex/LocallyConstantDerivative.lean) | In both actual fields, the indicator of the infinitesimal ideal is invariant under every infinitesimal increment, has fine derivative zero everywhere, and takes different values at zero and one. **Proved** for this counterexample; no connectedness of the actual domain is assumed. Build and axiom audit pass. |
| Quadratic-remainder argument in `trigonometry:prop:lift`; first differentiation prerequisite of `a:cor:complexsub` | `secondOrderRemainder`, `coeff_secondOrderRemainder`, `eq_linear_add_sq_mul_secondOrderRemainder` in [Algebra/PowerSeriesRemainder.lean](../Surreal/Algebra/PowerSeriesRemainder.lean); `powerSeriesSecondRemainder`, `powerSeriesEvaluation_eq_linear_add_sq_mul`, finite/residue and uniform bound theorems in [Surcomplex/PowerSeriesRemainder.lean](../Surreal/Surcomplex/PowerSeriesRemainder.lean); `powerSeriesFunction`, `fineHasDerivAt_powerSeriesFunction_zero`, `continuousAt_powerSeriesFunction_zero` in [PowerSeriesFineDerivative.lean](../Surreal/Surcomplex/PowerSeriesFineDerivative.lean) | Every real/complex formal series splits exactly into its constant, linear and quadratic-remainder terms. The actual remainder has residue equal to coefficient two and is uniformly bounded by that coefficient's ordinary magnitude plus one over all infinitesimal inputs. The evaluation function on the open infinitesimal domain has fine derivative at zero equal to the embedded linear coefficient. Its total zero extension only supplies a local function. **Proved at zero**, including arbitrary coefficient growth; re-expansion and differentiation at nonzero infinitesimals remain pending. Build and axiom audit pass. |
| Recentered Taylor rule `trigonometry:eq:lift`, sum/product and germ clauses of `trigonometry:prop:lift`; `found:rem:recentering` | `Surreal.Analytic.taylorSeries`, `hasFPowerSeriesAt_taylorSeries`, coefficient uniqueness, `taylorSeries_congr`, `_add`, `_mul`, `_const`, `_deriv` in [Algebra/AnalyticTaylor.lean](../Surreal/Algebra/AnalyticTaylor.lean); `analyticTaylorEvaluation`, its exact strong sum, finite/residue/center/germ/sum/product formulas, `analyticLift` and its corresponding formulas in [Surcomplex/AnalyticTaylor.lean](../Surreal/Surcomplex/AnalyticTaylor.lean) | Ordinary iterated derivatives divided by factorials are identified with Mathlib's actual convergent germ. An explicit ordinary complex analytic witness and actual infinitesimal displacement give the literal Taylor strong sum. Finite arguments are recentered at their standard part, with value and residue agreeing at the ordinary center. Germ equality, sums and products are preserved. **Proved for these complex univariate clauses**; real sign lifting, analytic composition, nonordinary-center differentiation and multivariable analytic lifting remain separate. Build and axiom audit pass. |
| Ordinary-center differentiation clause of `trigonometry:prop:lift` | `analyticTaylorFunction`, `fineHasDerivAt_analyticTaylorFunction`, `continuousAt_analyticTaylorFunction`, `analyticTaylorFunction_ofComplex_add`, `analyticTaylorFunction_standardPart_eq_analyticLift`, `analyticTaylorFunction_eq_analyticLift_of_isInfinitesimal` in [AnalyticFineDerivative.lean](../Surreal/Surcomplex/AnalyticFineDerivative.lean) | The translated Taylor function agrees with the witnessed and recentered analytic lift throughout its infinitesimal monad. At its ordinary center the fine derivative is the embedded ordinary complex derivative, using every positive surreal tolerance. **Proved at ordinary centers**; differentiation at nonordinary finite points remains pending. Build and axiom audit pass. |
| Finite Euler expression `trigonometry:eq:finiteEuler`; algebraic clauses of `trigonometry:thm:identities` | `finiteCos`, `finiteSin`, `finitePhase_eq_cos_add_sin_mul_I`, ordinary-constant, standard-part, finiteness, addition/subtraction, parity, period and double-angle formulas, `finitePhase_nsmul`, `finitePhase_zsmul`, `finiteCos_add_finiteSin_mul_I_zpow`, `finitePhase_eq_exp_mul_infExp`, `finitePhase_eq_exp_mul_strongSum` in [FiniteTrigonometry.lean](../Surreal/Surcomplex/FiniteTrigonometry.lean) | Phase coordinates on the explicit finite-angle domain obey Pythagoras, sine/cosine addition, parity, ordinary `2π` periodicity and integer de Moivre, and agree with ordinary trigonometry on real constants. Finite Euler is ordinary exponential times its literal infinitesimal exponential strong sum. **Proved for the phase-coordinate definition**; identification with the separate even/odd Taylor sums in `trigonometry:eq:sinfinite`/`cosfinite` and the derivative and order claims remain pending. The half-angle, sum-to-product, product-to-sum and Chebyshev identities are mapped in the finite-trigonometry identities row below. Build and axiom audit pass. |
| Native source summation and strong-additivity prerequisite for `thm:exact` | `PowerSeriesSummable`, `powerSeriesSum`, `powerSeriesEvaluationJointFamily`, `evaluatedPowerSeriesFamily`, `evaluate_powerSeriesSum` in [HahnSeries/StrongEvaluation.lean](../Surreal/HahnSeries/StrongEvaluation.lean); `powerSeriesSourceFamily`, `powerSeriesSummable_iff_exists_hahnFamily`, `powerSeriesSum_eq_toPowerSeries_hsum`, monomial and equivalence-reindexing identities in [PowerSeriesSummation.lean](../Surreal/HahnSeries/PowerSeriesSummation.lean) | Finite coefficient incidence is exactly native Hahn summability of ordinary formal series over natural exponents. Refining by source member and degree constructs a jointly summable family before regrouping, so positive-order evaluation preserves its exact coefficient sum. Monomial families reconstruct every formal series. **Proved** over arbitrary commutative coefficient rings and arbitrary index universes, including zero input, without a topology or no-zero-divisors assumption. Build and axiom audit pass. |
| Actual strong additivity and uniqueness clauses of `thm:exact` and the following prose | `stronglySummable_powerSeriesEvaluation`, `powerSeriesEvaluation_powerSeriesSum` in [Surcomplex/StrongEvaluation.lean](../Surreal/Surcomplex/StrongEvaluation.lean); `PowerSeriesStronglyAdditive`, `powerSeriesEvaluation_stronglyAdditive`, `powerSeriesHom_eq_of_stronglyAdditive`, `existsUnique_powerSeriesStrongHom`, real `exists_powerSeriesStrongHom_iff` in [PowerSeriesStrongHom.lean](../Surreal/Surcomplex/PowerSeriesStrongHom.lean) | Actual real and complex evaluation preserve source strong summability at every infinitesimal, and preserve actual sums with the explicit lower-universe-small index bound. Strong additivity on permitted index types, coefficient fixing and the variable image uniquely determine the map, by a lifted natural-index monomial family. The real existence criterion is exactly infinitesimality; complex existence/uniqueness retains that explicit hypothesis. **Proved**, including zero, without inferring uniqueness among arbitrary ring maps. Build and axiom audit pass. |
| All four alternatives of evaluation-at-omega `thm:exact` | `powerSeriesCoefficientAlgebra`, `powerSeriesEvaluationAlgHom`, `exists_real_powerSeriesAlgHom_iff`, `powerSeries_variable_image_equivalences` in [SignSequencePowerSeriesAlgebra.lean](../Surreal/Foundations/SignSequencePowerSeriesAlgebra.lean), with the preceding evaluation, strong-additivity and injectivity rows | The ordinary-real embedding explicitly supplies Mathlib’s coefficient algebra. Rational homomorphism existence, infinitesimality, a coefficient-fixing strongly additive real map, and native real-algebra homomorphism existence are equivalent. Canonical evaluation has the literal Hahn strong-sum formula and is injective for nonzero input. **All theorem clauses proved** on the universe-indexed actual carrier, with permitted strong-sum index size explicit. Universe-lift coherence remains separate. Build and axiom audit pass. |
| Explicit leading-term calculation in `rem:leading-inj` | `leadingCoeff_pow`, `leadingCoeff_eq_standardPart_of_valuation_zero`, `leadingCoeff_powerSeriesEvaluation`, `leadingExponent_powerSeriesEvaluation` in both namespaces in [PowerSeriesLeading.lean](../Surreal/Surcomplex/PowerSeriesLeading.lean) | For a nonzero formal series of order `m`, actual evaluation has leading coefficient `coeff m f * leadingCoeff x ^ m`; for nonzero infinitesimal input its growth exponent is `m • leadingExponent x`. The coefficient formula also includes zero input and the constant-degree case. **Proved** in both fields by the native formal unit factorization and actual residue and valuation formulas. Build and axiom audit pass. |
| Actual finite-exponential clauses of `e:prop-polar` | `infinitesimalPart`, `finiteExp`, `finiteExpHom`, `finiteExp_add`, `finiteExp_sub`, `standardPart_finiteExp`, `isFinite_finiteExp`, `exists_finiteExp_eq`, `finiteExpHom_surjective`, `finiteExp_eq_one_iff`, `finiteExp_eq_finiteExp_iff` in [Surcomplex/FiniteExponential.lean](../Surreal/Surcomplex/FiniteExponential.lean) | The actual finite exponential is ordinary complex exponential of standard part times the infinitesimal strong exponential. It is a group homomorphism onto the units of the actual finite subring, with exact kernel the ordinary integral multiples of `2πi`. Constants and infinitesimals retain their established exponentials. **Proved** on the explicit finite domain; infinite inputs and global exponential remain separate. Build and axiom audit pass. |
| Actual principal-angle assertions in the proof of `e:prop-polar` | `IsPrincipalAngle`, `principalAngle_eq_of_period`, `existsUnique_principalAngle_period`, `isPrincipalAngle_pi`, `finitePhase_pi`, `existsUnique_principal_polar`, `negative_real_polar_pi`, `principal_polar_angle_of_negative_real` in [Surcomplex/PolarNormalization.lean](../Surreal/Surcomplex/PolarNormalization.lean) | Every finite real surreal angle has a unique ordinary-period translate in the actual interval `(-π, π]`. Reducing standard part and correcting an infinitesimal excursion past the upper endpoint avoids any Archimedean assumption on the surreal field. Every actual nonzero surcomplex has a unique principal polar angle, and every negative real input has angle `π`, at infinite or infinitesimal scales as well. **Proved** for these finite-exponential assertions; no global trigonometric extension is assumed. Build and axiom audit pass. |
| Actual finite-angle polar clauses of `e:prop-polar`, `e:eq-polar` | `finiteConj`, `finiteImaginary`, `finiteExp_conj`, `finitePhase`, `modulus_finitePhase`, `finitePhase_eq_iff`, `exists_finitePhase_eq_of_modulus_eq_one`, `exists_polar`, `polar_angle_eq_iff` in [Surcomplex/Polar.lean](../Surreal/Surcomplex/Polar.lean) | Every actual nonzero surcomplex is its positive actual modulus times the finite exponential of a purely imaginary finite real angle. Two finite angles give the same phase exactly when their difference is an ordinary integral multiple of `2π`. Unit-circle surjectivity follows from finite-exponential surjectivity, conjugation and the exact kernel. Together with the finite-exponential row, **all proposition clauses of `e:prop-polar` are proved on the actual field**. Principal-interval normalization and the negative-real angle in the proof are established above. Build and axiom audit pass. |
| Homomorphism restrictions `thm:necessary`, `prop:kernel`, and their Archimedean consequences in evaluation-at-omega | `apply_eq_constantCoeff_of_X_eq_zero`, `injective_of_X_ne_zero`, `exists_unit_sq_of_constantCoeff_one`, `map_pos_of_constantCoeff_one`, `abs_map_X_lt_one_div`, `map_X_eq_zero_of_archimedean`, `apply_eq_constantCoeff_of_archimedean` in [PowerSeriesHom.lean](../Surreal/Algebra/PowerSeriesHom.lean) | A map killing the variable factors through its constant coefficient; a nonzero variable image forces injectivity. Over a characteristic-zero coefficient field, formal unit squares force every variable image in an ordered field to satisfy all strict reciprocal-natural bounds. In an Archimedean target it vanishes. **Proved** with no continuity, coefficient-fixing or strong-additivity premise. Build and axiom audit pass. |
| Full normalized-unit statement `lem:unit-root` in evaluation-at-omega | `existsUnique_sq_of_constantCoeff_one`, `existsUnique_inverse_of_constantCoeff_ne_zero` in [PowerSeriesUnitRoots.lean](../Surreal/Algebra/PowerSeriesUnitRoots.lean) | Every constant-one formal series over a characteristic-zero field has a unique constant-one square root. Every series with nonzero constant coefficient over any field has a unique two-sided inverse. **Proved** using native binomial series, formal substitution, units and the equal-squares identity. Build and axiom audit pass. |
| Algebraic existence and injectivity clauses of `thm:exact`; valuation part of `rem:leading-inj` in evaluation-at-omega | `isInfinitesimal_map_powerSeries_X`, `exists_rat_powerSeriesHom_iff`, `exists_real_powerSeriesHom_iff`, `powerSeriesEvaluation_injective`, `powerSeriesEvaluation_injective_iff`, `valuation_powerSeriesEvaluation` in [Surcomplex/PowerSeriesHom.lean](../Surreal/Surcomplex/PowerSeriesHom.lean) | An actual surreal occurs as the formal-variable image of a rational-series homomorphism exactly when infinitesimal; the same criterion gives a real-coefficient map fixing every ordinary real. Actual real and complex evaluation are injective exactly at nonzero infinitesimals. For nonzero formal series the value has valuation `order.toNat • valuation x`, including zero inputs. **Proved** for these clauses. Preservation of source-summable families, uniqueness among strongly additive maps, and explicit leading data are proved above. Build and axiom audit pass. |
| Actual infinitesimal exp/log summability, inverse and group laws of `e:prop-infexp` | `infExp`, `infLog`, `stronglySummable_infExp`, `stronglySummable_infLog`, strong-sum and standard-part formulas, `infLog_infExp_sub_one`, `infExp_infLog`, `infExp_add`, `infExp_neg`, `infLog_mul`, `infExp_injective`, `existsUnique_infExp_eq` in [SignSequenceExpLog.lean](../Surreal/Foundations/SignSequenceExpLog.lean) and [ExpLog.lean](../Surreal/Surcomplex/ExpLog.lean) | Ordinary formal exp/log evaluate as their exact actual real and complex strong sums. They are mutually inverse between infinitesimals and numbers infinitesimally close to one, with the exponential addition and logarithm product laws. Zero is included; `infLog x hx` means `log(1+x)`. **Proved** for these actual infinitesimal clauses. Global exponentials and logarithms remain separate. Build and axiom audit pass. |
| Actual group-isomorphism clause of `e:prop-infexp` | `infinitesimalAddSubgroup`, `infinitesimalUnitSubgroup`, `infExpEquiv`, `infExpEquiv_apply`, `infExpEquiv_symm_apply` in [ExpLogEquiv.lean](../Surreal/Surcomplex/ExpLogEquiv.lean) | Actual infinitesimal exp/log are bundled as inverse group equivalences from additive infinitesimals to multiplicative units infinitesimally close to one, in both fields. Subgroup inverse closure follows from the proved exp/log identities. Together with the actual summability, inverse and conjugation rows, **all clauses of `e:prop-infexp` are proved for actual surcomplex numbers**. This does not construct the report’s later global exponential or logarithm. Build and axiom audit pass. |
| Actual conjugation and unit-circle clauses of `e:prop-infexp` | `infinitesimal_conj`, `StronglySummable.conj`, `strongSum_conj`, `powerSeriesEvaluation_conj` in [StrongConjugation.lean](../Surreal/Surcomplex/StrongConjugation.lean); `infExp_conj`, `infLog_conj`, `conj_infLog_eq_neg_of_mul_conj_eq_one`, `infLog_re_eq_zero_of_mul_conj_eq_one`, `infLog_re_eq_zero_of_modulus_eq_one` in [ExpLogConjugation.lean](../Surreal/Surcomplex/ExpLogConjugation.lean) | Conjugation preserves actual strong summability and small strong sums; formal evaluation conjugates both the argument and ordinary coefficients. Actual infinitesimal exp/log commute with conjugation. The logarithm of a literal modulus-one element near one has zero real coordinate. **Proved** for all remaining conjugation and unit-circle clauses on the actual field. Build and axiom audit pass. |
| Actual binomial specialization of `a:cor:complexsub`; root branch used in `b:ramification` and local trigonometric expansions | `binomialPower`, `stronglySummable_binomialTerms`, `binomialPower_eq_strongSum`, finite/standard-part/near-one formulas, `binomialPower_add`, `_nat`, `_pow`, `_neg`, `_rat_root`, `_rat_root_unique`, `pow_injective_near_one`, `exists_unique_root_near_one`, workspace agreement; real `binomialPower_pos`, `binomialPower_half_eq_sqrt` in [SignSequenceBinomial.lean](../Surreal/Foundations/SignSequenceBinomial.lean) and [Binomial.lean](../Surreal/Surcomplex/Binomial.lean) | Actual binomial strong sums accept every ordinary real or complex exponent, with standard part one and exact exponent identities. For positive natural degree, the reciprocal-integer exponent gives the unique root near one among all actual candidates. Real binomial values are positive; the half-power is the existing genetic square root. Zero increments are included. **Proved** for these algebraic branch clauses; global powers, recentered analytic expansions and analytic ramification remain separate. Build and axiom audit pass. |
| Named-radius clause of `a:ex:geometric`; actual instances of `found:ex:archimedean` | `valuation_geometric_tMonomial_one_remainder`, `tMonomial_omega0_lt_abs_geometric_remainder`, `geometric_partialSum_not_mem_omega0_ball`, and complex modulus/fine-ball counterparts in [GeometricScale.lean](../Surreal/Surcomplex/GeometricScale.lean) | At `t = tMonomial 1`, every finite remainder has valuation `N+1`, strictly below the actual ordinal omega. Its actual absolute value or modulus strictly exceeds `t^ω`, excluding every finite partial sum from the explicitly named ball. **Proved**, completing the named-scale obligation for the actual geometric example. Intrinsic topology in a specified Hahn workspace remains separate. Build and axiom audit pass. |
| Actual geometric identity `a:eq:geom`; remainder, valuation and nonconvergence clauses of `a:ex:geometric` | `stronglySummable_powers`, `geometric_strongSum_mul`, `geometric_strongSum`, `geometric_strongSum_remainder`, `valuation_geometric_strongSum_remainder`, `geometric_partialSum_ne_strongSum`, `not_tendsto_geometric_partialSums` in both actual namespaces in [GeometricSeries.lean](../Surreal/Surcomplex/GeometricSeries.lean) | Every actual real or complex infinitesimal has geometric strong sum `(1-x)⁻¹`, with exact remainder `x^(N+1)/(1-x)` and valuation `(N+1) • valuation x`. Zero is included. For every nonzero input, finite geometric partial sums have no limit in the fine topology. **Proved** for these clauses; the explicitly named radius bound is proved above. Build and axiom audit pass. |
| Actual finite-variable summability, ring and composition clauses of `a:cor:complexsub` | `mvPowerSeriesEvaluation`, `stronglySummable_mvPowerSeries`, `mvPowerSeriesEvaluation_eq_strongSum`, `mvPowerSeriesEvaluation_hahnEmbedding`, `mvPowerSeriesEvaluation_monomial`, `_X`, `_C`, `isFinite_mvPowerSeriesEvaluation`, `standardPart_mvPowerSeriesEvaluation`, `isInfinitesimal_mvPowerSeriesEvaluation_iff`, `mvPowerSeriesEvaluation_subst` in [SignSequenceMvPowerSeries.lean](../Surreal/Foundations/SignSequenceMvPowerSeries.lean) and [MvPowerSeries.lean](../Surreal/Surcomplex/MvPowerSeries.lean) | Every ordinary real or complex formal series in finitely many variables evaluates at actual infinitesimal arguments as a ring homomorphism and the exact strong sum of its coefficient-times-monomial family. The result agrees with every small Hahn representation, is finite, and has the prescribed constant standard part. Zero-constant formal substitution commutes with evaluation. Empty variable types and zero inputs are included. **Proved** for these finite-variable clauses without coefficient-growth assumptions. Multivariable differentiation and recentered analytic Taylor lifting remain separate. Build and axiom audit pass. |
| Actual complex regrouping and interchange following `a:def:summable` | `Surreal.Surcomplex.StronglySummable.restrict`, `.reindex`, `.regroup`, `strongSum_reindex`, `strongSum_regroup`, `strongSum_fubini` in [StrongRegroup.lean](../Surreal/Surcomplex/StrongRegroup.lean) | Any restriction or bijective reindexing preserves joint strong summability. Grouping a small jointly summable family along an arbitrary index map gives strongly summable fiber sums and preserves the actual sum when the outer index is small. Projection-fiber regroupings of a jointly summable double family have equal sums. **Proved** with both smallness bounds explicit; existence of two iterated sums alone is not used to infer joint summability. Build and axiom audit pass. |
| Finite-sum consistency of `a:def:summable` and `found:eq:summability` | `stronglySummable_of_finite`, `strongSum_eq_sum` in both actual namespaces in [StrongFinite.lean](../Surreal/Surcomplex/StrongFinite.lean) | Every finite actual real or complex family meets both support conditions. Canonical strong summation equals the existing finite field sum, including empty families and cancellation. **Proved** by native finite-support Hahn families and the canonical extraction ring maps. Build and axiom audit pass. |
| Complex normal-form leading clauses of `a:eq:valuation`, `a:eq:modulusleading` | `Surreal.Surcomplex.hahnEmbedding_single`, `hahnEmbedding_C`, `leadingExponent_hahnEmbedding`, `normalized_hahnEmbedding`, `leadingCoeff_hahnEmbedding`, `leadingTerm_hahnEmbedding`, `exists_leading_error_hahnEmbedding`, `leadingCoeff_modulus_hahnEmbedding`, `valuation_sub_leading_hahnEmbedding` in [HahnLeading.lean](../Surreal/Surcomplex/HahnLeading.lean) | Actual complex Hahn evaluation preserves each monomial and its ordinary coefficient. Leading exponent and coefficient, normalized residue, leading term, and the modulus leading decomposition agree with the full native series. Zero is retained; deleting a nonzero leading term strictly raises valuation. **Proved** for arbitrary small ordered exponent groups and arbitrary supports, without a divisibility hypothesis. Build and axiom audit pass. |
| Complex small-family clause of `found:thm:workspace` | `Surreal.Surcomplex.familyCoordinateForms`, `familyWorkspaceEmbedding`, `familyHahnPreimage`, `familyWorkspaceEmbedding_preimage`, `familyWorkspaceSubfield`, `small_familyWorkspaceSubfield`, `familyWorkspaceEquiv` in [Workspace.lean](../Surreal/Surcomplex/Workspace.lean) | Both full coordinate normal forms of every member of any small actual complex family fit in one small divisible Hahn workspace. Explicit preimages reconstruct the inputs, and the whole workspace is isomorphic to a small actual subfield. **Proved** without a finite-support or summability restriction. Build and axiom audit pass. |
| Complex strong summability and sum clauses of `a:def:summable`, `found:eq:summability`, `found:thm:workspace` | `Surreal.Surcomplex.rawNormalForm`, `StronglySummable`, `stronglySummable_iff_re_im`, `strongSum`, `rawNormalForm_strongSum`, `coeff_rawNormalForm_strongSum`, `strongSum_hahnEmbedding` in [StrongSummation.lean](../Surreal/Surcomplex/StrongSummation.lean) | The complex canonical form pairs the two real canonical forms. Its joint-support well-ordering and finite fibers hold exactly when both coordinate families satisfy those conditions. The coordinate strong sum has exactly the native complex coefficient sum and agrees with every small workspace embedding. **Proved** with explicit lower-universe index smallness for actual sums; no topological summation is used. Build and axiom audit pass. |
| Algebra and real regrouping following `a:def:summable` | `rawNormalFormRingHom`, `StronglySummable.add`, `.neg`, `.mul`, `.const_mul`, `strongSum_add`, `strongSum_neg`, `strongSum_mul`, `strongSum_const_mul` in [SignSequenceStrongAlgebra.lean](../Surreal/Foundations/SignSequenceStrongAlgebra.lean) and [StrongAlgebra.lean](../Surreal/Surcomplex/StrongAlgebra.lean); `StronglySummable.restrict`, `.reindex`, `.regroup`, `strongSum_reindex`, `strongSum_regroup` in [SignSequenceStrongRegroup.lean](../Surreal/Foundations/SignSequenceStrongRegroup.lean) | Real and complex canonical extraction are ring maps. Native family operations prove summability and sum laws for addition, negation, products over independent index types, and arbitrary fixed actual scalars. Real jointly summable families restrict and regroup along arbitrary index maps; small fibers and outer indices give unchanged actual sums. **Proved** for these clauses, retaining joint summability and smallness. Build and axiom audit pass. |
| Actual constant-family clause of `a:rule:clauseii`; nonsummability in `a:ex:notsummable` and `found:ex:failed` | `Surreal.Foundations.SignSequence.stronglySummable_ofReal_iff`, `strongSum_ofReal`, `not_stronglySummable_ofReal`; `Surreal.Surcomplex.stronglySummable_ofComplex_iff`, `strongSum_ofComplex`, `not_stronglySummable_ofComplex`, `not_stronglySummable_geometric_constants` in [StrongConstants.lean](../Surreal/Surcomplex/StrongConstants.lean) | Ordinary real and complex constant families are strongly summable exactly when only finitely many are nonzero, and their actual sums are the embedded finite coefficient sums. Infinitely many nonzero constants, including `2⁻ⁿ`, fail the coefficient-fiber condition. **Proved** for these constant assertions; the separate decreasing-positive-exponent example and ordinary analytic convergence are not asserted here. Build and axiom audit pass. |
| Actual univariate summability, ring and composition clauses of `a:cor:complexsub` | `powerSeriesEvaluation`, `stronglySummable_coeff_mul_powers`, `powerSeriesEvaluation_eq_strongSum`, `powerSeriesEvaluation_hahnEmbedding`, `powerSeriesEvaluation_X`, `_C`, `_zero`, `isFinite_powerSeriesEvaluation`, `standardPart_powerSeriesEvaluation`, `isInfinitesimal_powerSeriesEvaluation_iff`, `powerSeriesEvaluation_subst` in [SignSequencePowerSeries.lean](../Surreal/Foundations/SignSequencePowerSeries.lean) and [PowerSeries.lean](../Surreal/Surcomplex/PowerSeries.lean) | Every ordinary real or complex formal coefficient sequence gives strongly summable displayed terms at any actual infinitesimal, including zero. Evaluation is a ring homomorphism equal to that actual strong sum and agrees with every small Hahn representation. Values are finite with the prescribed standard part. Formal composition commutes with evaluation when the inner constant coefficient vanishes. **Proved** for these univariate clauses without coefficient-growth hypotheses; finite multivariate evaluation is proved above; differentiation at zero and ordinary-center analytic germ lifting are proved above; general differentiation and coherent fixed-domain lifting remain separate. Build and axiom audit pass. |
| Actual small-family localization in `found:thm:workspace` | `Surreal.Foundations.SignSequence.familyWorkspaceEmbedding`, `familyHahnPreimage`, `familyWorkspaceEmbedding_preimage`, `familyWorkspaceSubfield`, `small_familyWorkspaceSubfield`, `exists_polynomial_hahn_preimage_natDegree` in [SignSequenceWorkspace.lean](../Surreal/Foundations/SignSequenceWorkspace.lean) | Canonical extraction places every lower-universe-small actual family in one small divisible real Hahn workspace. Its actual image is a small subfield containing every input. Explicit preimages give polynomial descent with exact degree preservation. **Proved** for these real-family clauses, including empty families. No single workspace containing all surreals is asserted. Build and axiom audit pass. |
| Algebraic-closedness clause of `found:prop:complex`; actual root and factorization clauses of `polynomial:thm:fta` | `Surreal.Surcomplex.hahnEmbedding`, `polynomialWorkspaceEmbedding`, `coeff_mem_range_polynomialWorkspaceEmbedding`, `exists_polynomial_hahn_preimage`, `exists_isRoot_of_natDegree_pos`, `surcomplexIsAlgClosed`, `polynomial_splits`, `polynomial_factorization`, `polynomial_roots_card` in [Surcomplex/AlgebraicallyClosed.lean](../Surreal/Surcomplex/AlgebraicallyClosed.lean) | The real Hahn embedding extends coordinatewise through the native complex Hahn equivalence. One small divisible exponent group contains both coordinate normal forms of every polynomial coefficient. Injective descent preserves degree, and algebraic closedness of the constructed complex Hahn workspace supplies an actual root. Thus the actual surcomplex field is unconditionally algebraically closed; all polynomials split and have the stated linear factorization and total root multiplicity, with zero/constants handled by the native conventions. **Proved** for these clauses, without assuming target closedness. Build and axiom audit pass. |
| Full Hahn interpretation of `a:eq:valuation`, `a:eq:st`, and residue clauses of `found:thm:workspace` | `Surreal.Foundations.SignSequence.valuation_hahnEmbedding`, `leadingCoeff_hahnEmbedding`, `isFinite_hahnEmbedding_iff`, `isInfinitesimal_hahnEmbedding_iff`, `standardPart_hahnEmbedding` in [SignSequenceHahnValuation.lean](../Surreal/Foundations/SignSequenceHahnValuation.lean); the valuation, finiteness, infinitesimality and standard-part counterparts in [Surcomplex/HahnValuation.lean](../Surreal/Surcomplex/HahnValuation.lean) | On arbitrary Hahn supports, actual valuation is the exponent embedding applied to the native least exponent, including infinity at zero. Real leading coefficients agree. Nonnegative/positive Hahn order characterizes finite/infinitesimal actual values, and the actual standard part on the finite domain is exactly the zero coefficient. Complex valuation uses the minimum of the two coordinate orders. **Proved** for these real and complex embedding clauses; complex leading-coefficient compatibility is proved above. Build and axiom audit pass. |
| Exponent-workspace coherence of the actual bridge in `found:thm:workspace` | `Surreal.Foundations.SmallNormalForm.hahnEmbedding_workspaceEmbedding`, `Surreal.Foundations.SignSequence.hahnEmbedding_workspaceEmbedding`, `hahnEmbedding_comp_workspaceEmbedding` in [SignSequenceHahnCoherence.lean](../Surreal/Foundations/SignSequenceHahnCoherence.lean); `Surreal.HahnSeries.workspaceEmbedding_realComplexHahnEquiv` and the actual complex counterparts in [Surcomplex/HahnCoherence.lean](../Surreal/Surcomplex/HahnCoherence.lean) | Enlarging the small exponent workspace and then evaluating agrees exactly with evaluating along the composite exponent map, as values and as ring homomorphisms. Formal coefficient comparison includes exponents outside either image; the complex proof transports both coordinates. **Proved** for arbitrary supports and independent exponent-type universes. Coherence under lifting the actual surreal birthday universe remains pending. Build and axiom audit pass. |
| Real strong summability in `found:eq:summability` and strong-sum clause of `found:thm:workspace` | `Surreal.Foundations.SignSequence.rawNormalForm`, `StronglySummable`, `StronglySummable.small_support_hsum`, `strongSum`, `normalForm_strongSum`, `coeff_normalForm_strongSum`, `stronglySummable_hahnEmbedding`, `strongSum_hahnEmbedding` in [SignSequenceStrongSummation.lean](../Surreal/Foundations/SignSequenceStrongSummation.lean) | Strong summability requires a partially well-ordered union of canonical normal-form supports and finite coefficient fibers. A lower-universe-small index type makes the native sum support small, so canonical evaluation gives an actual strong sum with exactly the finite coefficient sums. Every native real Hahn summable family remains strongly summable after embedding, and the embedding commutes with its small strong sum. **Proved** for these real clauses, with explicit index smallness for the sum. Complex strong sums are proved above; the remaining analytic-operation correspondences and universe coherence are pending; no topological convergence is asserted. Build and axiom audit pass. |
| Finite arithmetic and comparison prerequisites of `found:eq:normalform`, `found:thm:workspace` | `Surreal.Foundations.SignSequence.leading_finite_monomial_sum`, `finiteMonomialEvaluation`, `finiteMonomialEvaluation_comp_mapDomainRingHom`, `finiteMonomialEvaluation_leading`, `finiteMonomialEvaluation_injective`, `leadingCoeff_finiteMonomialEvaluation`, `valuation_finiteMonomialEvaluation`, `finiteMonomialEvaluation_pos_iff` in [SignSequenceFiniteLeading.lean](../Surreal/Foundations/SignSequenceFiniteLeading.lean), [SignSequenceMonomialAlgebra.lean](../Surreal/Foundations/SignSequenceMonomialAlgebra.lean), [SignSequenceFiniteNormalForm.lean](../Surreal/Foundations/SignSequenceFiniteNormalForm.lean) | Finite real monomial expressions evaluate by a genuine ring homomorphism in the constructed sign field. Every strictly increasing additive exponent map gives injectivity; the least nonzero coefficient determines the actual valuation and leading coefficient. These agree with the corresponding finite Hahn series, including the zero case, and positivity agrees with Hahn lexicographic order. Finite evaluation commutes with additive exponent reindexing, including collisions. **Prerequisites proved** for finite supports; the canonical infinite ordered field isomorphism and finite-evaluation agreement are proved below; strong evaluation remains pending. Build and axiom audit pass. |
| Finite-support representation prerequisite of `found:thm:workspace` | `Surreal.HahnSeries.finiteSupportEmbedding`, `coeff_finiteSupportEmbedding`, `finiteSupportEmbedding_eq_ofFinsupp`, `finiteSupportEmbedding_injective`, `mem_range_finiteSupportEmbedding`, `existsUnique_finiteSupport_preimage` in [FiniteSupport.lean](../Surreal/HahnSeries/FiniteSupport.lean) | The additive monoid algebra embeds as a ring in the native Hahn series over any commutative semiring. Coefficients are preserved exactly, and its image consists precisely of the finite-support series, each with a unique coefficient representation. **Prerequisites proved**; this does not construct an infinite evaluation into the sign field. Build and axiom audit pass. |
| Exponent-enlargement compatibility clauses of `found:thm:workspace` | `Surreal.HahnSeries.workspaceEmbedding`, `support_workspaceEmbedding`, `orderTop_workspaceEmbedding`, `mapExponentsFamily`, `hsum_mapExponentsFamily`, `workspaceEmbedding_evaluate`, `workspaceEmbedding_mvEvaluate`, `workspaceEmbeddingNonnegative`, `standardPart_comp_workspaceEmbedding` in [WorkspaceEmbedding.lean](../Surreal/HahnSeries/WorkspaceEmbedding.lean) | Every strictly increasing additive exponent map induces an injective Hahn algebra homomorphism preserving exact supports and valuations. Strongly summable families transport with proved partially well-ordered support and finite coefficient fibers; their Hahn sums commute with the embedding. Admissible univariate and finite-variable evaluation, valuation rings and standard part are compatible. **Proved** for Hahn-to-Hahn embeddings; actual embeddings, small real-family localization, complex small-family localization, and exponent-workspace coherence are proved above; the remaining analytic-operation transport is separate. Build and axiom audit pass. |
| Strong summability and inverse clauses of `e:prop-infexp` | `Surreal.FormalPowerSeries.log_subst_exp_sub_one`, `exp_subst_log` in [PowerSeriesExpLog.lean](../Surreal/Algebra/PowerSeriesExpLog.lean); `Surreal.HahnSeries.infExp`, `infLog`, `infExpFamily`, `infLogFamily`, their term and Hahn-sum formulas, `infExp_sub_one_pos`, `infLog_orderTop_pos`, `infLog_infExp_sub_one`, `infExp_infLog`, `infExp_injective`, `existsUnique_infExp_eq` in [ExponentialLogarithm.lean](../Surreal/HahnSeries/ExponentialLogarithm.lean) | Over any characteristic-zero coefficient field and ordered abelian exponent group, the displayed exponential and logarithmic terms form actual strongly summable families. Formal derivative and substitution arguments prove both inverse identities after admissible evaluation. Every series differing from one by positive order has a unique infinitesimal logarithm. Zero input is included. **Prerequisites proved** in the Hahn workspace; the group law and conjugation are mapped below, and their actual real/complex interpretation is proved above. Build and axiom audit pass. |
| Group-isomorphism clauses of `e:prop-infexp` | `Surreal.HahnSeries.infExpFamily_add`, `infExp_add`, `infExp_zero`, `infExp_neg`, `positiveOrderAddSubgroup`, `infExpEquiv` in [ExponentialAddition.lean](../Surreal/HahnSeries/ExponentialAddition.lean) | The product of the two actual exponential families is jointly strongly summable. Regrouping by total degree and the native formal exponential coefficient identity prove the addition law. Exponential and logarithm form a group isomorphism from the additive positive-order subgroup to the native multiplicative group of units differing from one by positive order. No topological limit or inadmissible unit substitution is used. **Proved** in the Hahn workspace; the actual infinitesimal group laws are proved above. Build and axiom audit pass. |
| Coefficient-map compatibility of strong evaluation; conjugation and algebraic unit-circle clauses of `e:prop-infexp` | `Surreal.HahnSeries.mapCoefficients`, `mapCoefficientsFamily`, `mapCoefficients_hsum`, `mapCoefficients_evaluate` in [CoefficientMapping.lean](../Surreal/HahnSeries/CoefficientMapping.lean); `mapCoefficients_infExp`, `mapCoefficients_infLog`, `complexConjugation_infExp`, `complexConjugation_infLog`, `complexConjugation_infLog_eq_neg_of_mul_conj_eq_one`, `infLog_re_eq_zero_of_mul_conj_eq_one` in [ExponentialConjugation.lean](../Surreal/HahnSeries/ExponentialConjugation.lean) | An arbitrary coefficient ring homomorphism preserves both strong summability conditions, Hahn sums and positive-order formal evaluation, even if it removes leading terms. Complex conjugation commutes with exp/log. If a series differs from one by positive order and satisfies `z * conj(z) = 1`, every coefficient of its logarithm has real part zero. **Proved** for these Hahn statements; the literal Hahn modulus-one specialization is proved below, and actual conjugation and the unit-circle logarithm are proved above. Build and axiom audit pass. |
| Full finite comparison in `found:eq:normalform` and finite arithmetic in `found:thm:workspace` | `Surreal.Foundations.SignSequence.finiteMonomialEvaluation_eq_iff`, `finiteMonomialEvaluation_lt_iff`, `finiteMonomialEvaluation_le_iff`, `finiteMonomialEvaluation_lt_iff_coeff`, `finiteHahnSubring`, `mem_finiteHahnSubring`, `finiteHahnOrderRingEquiv`, `finiteHahnOrderEmbedding` in [SignSequenceFiniteOrder.lean](../Surreal/Foundations/SignSequenceFiniteOrder.lean) | Equality and both order comparisons of actual finite monomial expressions agree with the associated Hahn expressions. The first differing coefficient decides strict order. The native lexicographic Hahn subring with exactly finite support is isomorphic as an ordered ring to the actual finite-evaluation range and order embeds into the full sign field. **Proved** for finite normal forms; no infinite-support claim is made. Build and axiom audit pass. |
| Actual surcomplex finite arithmetic and leading-data clauses of `found:eq:normalform`, `a:eq:valuation`, `found:thm:workspace` | `Surreal.Surcomplex.leadingCoeff_add_of_valuation_lt`, `leading_finite_monomial_sum` in [Surcomplex/FiniteLeading.lean](../Surreal/Surcomplex/FiniteLeading.lean); `finiteMonomialEvaluation`, `finiteMonomialEvaluation_leading`, `finiteMonomialEvaluation_injective`, `valuation_finiteMonomialEvaluation`, `leadingCoeff_finiteMonomialEvaluation` in [Surcomplex/FiniteNormalForm.lean](../Surreal/Surcomplex/FiniteNormalForm.lean) | A higher-valuation summand does not change the actual complex leading coefficient. Finite complex normal forms evaluate by an injective ring homomorphism for every strictly increasing additive exponent map into the actual sign field. Valuation and leading coefficient agree exactly with the corresponding finite Hahn series, including zero. **Proved** for finite supports; infinite surcomplex Hahn field evaluation is proved below, with full strong-sum compatibility proved above. Build and axiom audit pass. |
| Literal unit-circle logarithm clause of `e:prop-infexp`; fixed-Hahn modulus prerequisites of `e:prop-polar` | `Surreal.HahnSeries.complexHahnLexEquiv`, `complexModulus`, its nonnegative, square, zero, product and triangle properties, `complexModulus_eq_one_iff`, `complexConjugation_infLog_eq_neg_of_modulus_eq_one`, `infLog_re_eq_zero_of_modulus_eq_one` in [HahnSeries/Modulus.lean](../Surreal/HahnSeries/Modulus.lean) | Over divisible ordered abelian exponents, complex Hahn series are identified with the quadratic extension of lexicographically ordered real Hahn series. The already constructed real Hahn square roots supply a real-Hahn-valued modulus. Its unit circle is exactly `z * conj(z) = 1`; hence the logarithm of every near-one modulus-one series has purely imaginary coefficients. Together with the preceding summability, inverse, group and conjugation results, this establishes **all clauses of `e:prop-infexp` in the fixed Hahn workspace**. The actual infinitesimal clauses are proved above. Build and axiom audit pass. |
| Exponent-group construction and size clauses in the proof of `found:thm:workspace`; exponent-level non-cover assertion of `found:rem:nocover` | `Surreal.Foundations.SignSequence.workspaceExponents`, `small_workspaceExponents`, `nontrivial_workspaceExponents`, `divisible_workspaceExponents`, `workspaceExponentInclusion`, `small_common_workspaceExponents`, `exists_not_mem_workspaceExponents`, `RealHahnWorkspace`, `ComplexHahnWorkspace` and their smallness and closedness results in [SignSequenceWorkspaceExponents.lean](../Surreal/Foundations/SignSequenceWorkspaceExponents.lean) | The actual rational span of a lower-universe-small surreal exponent set together with one is small, nonzero and divisible. Smallness follows from finite rational linear combinations, not an assumption on the ambient sign field. Inclusion induces a strictly increasing additive map, and a small family of small sets admits a common such enlargement. No single generated small exponent group contains all surreal exponents. The real and complex Hahn fields on this group are also lower-universe-small and inherit the constructed real/algebraic closedness instances. **Prerequisites proved**; localizing arbitrary actual surreal/surcomplex elements in these fields still requires their infinite normal forms. Build and axiom audit pass. |
| Finite-exponential homomorphism, surjectivity and kernel clauses of `e:prop-polar` | `Surreal.HahnSeries.infinitesimalPart`, `finiteExp`, `finiteExp_add`, `coeff_zero_finiteExp`, `finiteExpHom`, `exists_finiteExp_eq`, `finiteExpHom_surjective`, `finiteExp_eq_one_iff`, `finiteExp_eq_finiteExp_iff` in [FiniteExponential.lean](../Surreal/HahnSeries/FiniteExponential.lean) | On the nonnegative-order complex Hahn ring, finite exponentiation is the ordinary exponential of standard part times the strongly summable infinitesimal exponential. It is a homomorphism onto every unit of that ring. An explicit preimage uses an ordinary logarithm of the nonzero residue and the infinitesimal logarithm of the normalized principal unit. Its kernel is exactly the constant integral multiples of `2πi`; two inputs have equal exponentials precisely when their difference is such a constant. No nonzero infinitesimal period is admitted. **Proved** for these fixed-Hahn clauses; finite-angle polar representation and angle uniqueness are proved below; the actual finite exponential and polar statements are proved above. Build and axiom audit pass. |
| Modulus and residue prerequisites of `e:prop-polar`; fixed-Hahn counterparts of `a:eq:st` and `a:eq:valuation` | `Surreal.HahnSeries.complexModulus_single_zero`, `complexRealEmbedding_complexModulus_sq`, `orderTop_complexModulus`, `coeff_zero_complexModulus`, `orderTop_eq_zero_of_complexModulus_eq_one`, `norm_coeff_zero_eq_one_of_complexModulus_eq_one`, coordinate bounds in [ModulusStandardPart.lean](../Surreal/HahnSeries/ModulusStandardPart.lean) | The complex Hahn modulus has exactly the order of its input, including infinity at zero. For nonnegative-order input, its zero coefficient is the ordinary norm of the input's zero coefficient. Constant moduli and the real-axis absolute-value formula agree with their embeddings. Modulus-one series therefore have order zero and ordinary modulus-one standard part. The real and imaginary coordinates are bounded by the real-Hahn-valued modulus. **Proved** in divisible Hahn workspaces; the infinite actual-surcomplex interpretation remains pending. Build and axiom audit pass. |
| Finite-angle polar clauses of `e:prop-polar`, `e:eq-polar` | `Surreal.HahnSeries.imaginaryHahn`, `finiteImaginary`, `finiteExp_finiteImaginary_eq_iff`, `exists_finiteImaginary_exp_eq_of_modulus_eq_one`, `exists_finite_polar`, `finite_polar_angles_eq_iff` in [Polar.lean](../Surreal/HahnSeries/Polar.lean) | Every nonzero complex Hahn series over divisible exponents is its constructed positive real-Hahn modulus times the finite exponential of an imaginary finite real angle. The angle is obtained from the ordinary argument of the unit's residue plus the purely imaginary logarithm of its principal-unit part. Two finite real angles give the same phase exactly when their difference is a constant integral multiple of `2π`. Together with finite-exponential surjectivity and kernel, **all proposition clauses are proved in the fixed Hahn workspace**. Interval normalization is proved below; the actual finite exponential and polar statements are proved above. Build and axiom audit pass. |
| Principal-angle clauses of the proof of `e:prop-polar`; fixed-Hahn counterpart of `trigonometry:thm:polar` | `Surreal.HahnSeries.IsPrincipalAngle`, `existsUnique_principalAngle_period`, `existsUnique_principal_polar`, `negative_real_polar_pi`, `principal_polar_angle_of_negative_real` in [PolarNormalization.lean](../Surreal/HahnSeries/PolarNormalization.lean) | Every finite real Hahn angle has exactly one ordinary-period translate in the actual lexicographic interval `(-π, π]`. Reduction of the ordinary standard part is followed by an endpoint correction determined in Hahn order, so infinitesimal excursions beyond `π` are handled. Every nonzero complex Hahn series therefore has a unique principal polar angle, and every negative real input, at any scale, has angle `π`. **Proved** in divisible Hahn workspaces; actual principal-angle normalization is proved above. Build and axiom audit pass. |
| Small formal carrier and ordinal-truncation prerequisites of `found:eq:normalform`, `found:sub:bridge` | Pinned `SurrealHahnSeries` in [vendored HahnSeries/Basic.lean](../vendor/combinatorial-games/CombinatorialGames/Surreal/HahnSeries/Basic.lean); `Surreal.Foundations.SmallNormalForm`, `coeff`, `support`, `small_support`, `wellFoundedOn_support`, `length`, `exponent`, `coefficientAt`, `term`, `trunc`, `truncIdx`, `length_truncIdx_lt` in [SmallNormalForm.lean](../Surreal/Foundations/SmallNormalForm.lean) | Reuses the upstream ordered field of lower-universe-small formal real Hahn series without source modifications. Growth exponents are indexed by the actual sign field through the proved sign/game equivalence; their support is explicitly small and reverse well ordered. Ordinal enumeration, nonzero indexed coefficients, actual individual monomial terms, and strictly shorter support truncations are exposed. **Prerequisites proved**; a canonical cut candidate is constructed below, while its field identification remains pending. The audit now checks the upstream `SurrealHahnSeries` namespace as well. Build and axiom audit pass. |
| Approximation and simplest-limit prerequisites of `found:eq:normalform`, `found:sub:bridge` | `Surreal.Foundations.SignSequence.isInfinitesimal_div_tMonomial_iff`, `valuation_gt_iff_forall_nat_abs_lt`, `valuation_sub_gt_iff_forall_nat_between` in [SignSequenceValuationBounds.lean](../Surreal/Foundations/SignSequenceValuationBounds.lean); `valuationBallCut`, `simplestValuationBallPoint`, `simplestValuationBallPoint_mem`, `simplestValuationBallPoint_isPrefix`, `existsUnique_simplest_valuationBall_point` in [SignSequenceValuationBalls.lean](../Surreal/Foundations/SignSequenceValuationBalls.lean); `exists_larger_same_valuation_approximations`, `not_existsUnique_valuation_approximations` in [SignSequenceValuationApproximation.lean](../Surreal/Foundations/SignSequenceValuationApproximation.lean) | A strict valuation threshold is exactly all reciprocal-natural monomial bounds. Pairwise compatible balls indexed by a lower-universe-small type give a separated small cut, whose actual value meets every bound and is a prefix of every solution. This characterizes a unique simplest point, including zero for an empty family. A distinct larger solution to any small approximation family is constructed by adding a positive monomial beyond all thresholds, proving that the approximation inequalities alone are never a uniqueness principle. **Prerequisites proved** without real-closedness or an infinite normal-form assumption; the recursive candidate is constructed below; its arithmetic is proved below. Build and axiom audit pass. |
| Recursive cut candidate for `found:eq:normalform`, `found:sub:bridge` | `Surreal.Foundations.SmallNormalForm.support_trunc`, `trunc_trunc`, `trunc_exponent_zero`, `truncIdx_succ` in [SmallNormalFormTruncation.lean](../Surreal/Foundations/SmallNormalFormTruncation.lean); `cutEvaluation`, `cutEvaluation_centers_compatible`, `cutEvaluation_remainder`, `cutEvaluation_isPrefix`, `existsUnique_simplest_cutEvaluation` in [SmallNormalFormEvaluation.lean](../Surreal/Foundations/SmallNormalFormEvaluation.lean) | Recursion on the strictly smaller ordinal support length constructs an actual sign-sequence candidate for every small formal form. Earlier recursion proves pairwise compatibility of all truncation-plus-term centers, so the guarded fallback is never used. At each supported exponent the candidate differs from its recursive center by strictly higher valuation and is a prefix of every simultaneous solution. The empty form gives zero. **Candidate construction proved**; comparison, inverse extraction and arithmetic preservation are proved below; small real strong-sum compatibility is proved below; complex strong sums and univariate formal evaluation are proved above; recentered complex univariate lifting is proved above; its remaining analytic-operation correspondences are pending. No uniqueness of arbitrary approximation solutions is assumed. Build and axiom audit pass. |
| Leading data and negation of the recursive candidate | `Surreal.Foundations.SignSequence.leadingTerm`, `valuation_lt_sub_leadingTerm`, `leading_of_valuation_sub_omega_gt`, `valuation_sub_omega_gt_iff` in [SignSequenceLeadingTerm.lean](../Surreal/Foundations/SignSequenceLeadingTerm.lean); `Surreal.Foundations.SmallNormalForm.leading_cutEvaluation`, `valuation_cutEvaluation`, `leadingCoeff_cutEvaluation`, `cutEvaluation_eq_zero_iff`, `cutEvaluation_pos_iff`, `cutEvaluation_nonneg_iff` in [SmallNormalFormLeading.lean](../Surreal/Foundations/SmallNormalFormLeading.lean); `cutEvaluation_neg` in [SmallNormalFormNegation.lean](../Surreal/Foundations/SmallNormalFormNegation.lean) | Removing the actual leading term strictly raises valuation, and a sufficiently accurate monomial approximation determines actual leading data. The empty first truncation therefore identifies the candidate's leading exponent and coefficient with the formal first term. Actual and native Hahn leading coefficients agree, so zero and sign are preserved and reflected. Length induction and both prefix comparisons prove negation preservation on arbitrary small supports. **Prerequisites proved**; these results alone do not prove full injectivity, order embedding or preservation of addition and multiplication. Build and axiom audit pass. |
| Full comparison and exact constants for canonical small-form evaluation | `Surreal.Foundations.SmallNormalForm.cutEvaluation_trunc_isPrefix`, `cutEvaluation_remainder_all` in [SmallNormalFormCutTruncation.lean](../Surreal/Foundations/SmallNormalFormCutTruncation.lean); `leading_cutEvaluation_sub`, `cutEvaluation_injective`, `cutEvaluation_lt_iff`, `cutEvaluation_le_iff`, `cutEvaluationOrderEmbedding`, `valuation_cutEvaluation_sub` in [SmallNormalFormComparison.lean](../Surreal/Foundations/SmallNormalFormComparison.lean); `cutEvaluation_single_isPrefix`, `cutEvaluation_single_zero` in [SmallNormalFormConstants.lean](../Surreal/Foundations/SmallNormalFormConstants.lean) | The residual estimate extends to every growth exponent by selecting the greatest remaining support element, or proving that the truncation is the whole form. At the greatest formal difference, the two earlier truncations agree; subtracting the estimates identifies actual difference leading data, proving injectivity and full order comparison without assuming additivity. Every real constant evaluates exactly, by finite-birthday rigidity of real prefixes. Every singleton candidate is a prefix of its actual monomial. **Proved** for arbitrary small supports; exact arbitrary real-coefficient monomial evaluation and arithmetic compatibility are proved below. Build and axiom audit pass. |
| Conway-monomial compatibility of canonical evaluation | `Surreal.Foundations.SignSequence.omegaPower_isPrefix_of_pos_of_valuation_eq`, `Surreal.Foundations.SmallNormalForm.cutEvaluation_single_one` in [SmallNormalFormMonomials.lean](../Surreal/Foundations/SmallNormalFormMonomials.lean) | The native omega cut is a prefix of every positive actual surreal of the same valuation: its left and right options have strictly separated Archimedean classes. Combining this with the singleton candidate's opposite prefix relation proves exact evaluation of every formal unit-coefficient monomial as the actual Conway omega power. **Proved**; arbitrary real coefficients and arithmetic preservation are proved below. Build and axiom audit pass. |
| Birthday bound, initial segments and extension prerequisites of normal-form extraction | `Surreal.Foundations.SmallNormalForm.length_le_birthday_cutEvaluation` in [SmallNormalFormBirthday.lean](../Surreal/Foundations/SmallNormalFormBirthday.lean); `IsInitialSegment`, `exists_trunc_of_ne`, `length_lt`, `trunc_eq` in [SmallNormalFormInitialSegment.lean](../Surreal/Foundations/SmallNormalFormInitialSegment.lean); prefix and center compatibility in [SmallNormalFormInitialEvaluation.lean](../Surreal/Foundations/SmallNormalFormInitialEvaluation.lean); `Approximates`, `Approximates.leadingExponent_lt`, `residualExtension`, `Approximates.extend`, `Approximates.exists_strict_extension` in [SmallNormalFormExtension.lean](../Surreal/Foundations/SmallNormalFormExtension.lean) | Proper formal truncations give proper evaluated sign prefixes, so support length is bounded by candidate birthday. A partial approximation requires the target to meet every recursive center bound; mere prefix inclusion is insufficient. A nonzero residual then has growth exponent below every retained exponent, and appending its leading term preserves all bounds while strictly extending the evaluated prefix. Formal initial segments are equal forms or supported-exponent truncations, and restrict target bounds. **Proved** without evaluation additivity or an assumed transfinite termination theorem. Build and axiom audit pass. |
| Canonical order and inverse-extraction part of `found:eq:normalform`, `found:sub:bridge` | `Surreal.Foundations.SmallNormalForm.partialBirthdayEmbedding`, `small_partialApproximations` in [SmallNormalFormPartialChain.lean](../Surreal/Foundations/SmallNormalFormPartialChain.lean); `fromCoefficients`, `chainUnion`, `support_chainUnion`, `isInitialSegment_chainUnion`, `exists_stage_of_mem_support_chainUnion` in [SmallNormalFormUnion.lean](../Surreal/Foundations/SmallNormalFormUnion.lean); `approximates_chainUnion`, `cutEvaluation_surjective`, `cutEvaluationOrderIso`, `normalForm`, `cutEvaluation_normalForm`, `normalForm_cutEvaluation`, `normalForm_neg`, `normalForm_ofReal`, `normalForm_omegaPower` in [SmallNormalFormExtraction.lean](../Surreal/Foundations/SmallNormalFormExtraction.lean) | All partial approximations to a fixed surreal inject by evaluated birthday into its bounded ordinal interval, proving lower-universe smallness before maximality is used. Small chains of formal initial segments have reverse-well-ordered unions; each retained center already occurs in a stage, preserving the target constraints. Mathlib's general-relation Zorn lemma gives a maximal partial form, whose residual must vanish by the strict-extension theorem. Thus canonical cut evaluation is an order isomorphism onto the actual sign carrier, with inverse extraction and zero/negation/real-constant/Conway-monomial formulas. **Proved** for the canonical order/extraction construction. The separate arithmetic proofs below upgrade this map to an ordered field isomorphism; small real strong-sum compatibility is proved below; complex strong sums and univariate formal evaluation are proved above; recentered complex univariate lifting is proved above; its remaining analytic-operation correspondences are pending. Build and axiom audit pass. |
| Real monomials, addition and finite-evaluation agreement in `found:eq:normalform`, `found:sub:bridge` | `Surreal.Foundations.SignSequence.real_mul_omegaPower_isPrefix_of_valuation_sub_gt`, `Surreal.Foundations.SmallNormalForm.cutEvaluation_single` in [SmallNormalFormRealMonomials.lean](../Surreal/Foundations/SmallNormalFormRealMonomials.lean); `sum_isPrefix_of_sub_realizes`, `cutEvaluation_add_isPrefix_of_approximates` in [SignSequenceSumCutSimplicity.lean](../Surreal/Foundations/SignSequenceSumCutSimplicity.lean) and [SmallNormalFormSumSimplicity.lean](../Surreal/Foundations/SmallNormalFormSumSimplicity.lean); `cutEvaluation_add` in [SmallNormalFormAddition.lean](../Surreal/Foundations/SmallNormalFormAddition.lean); `cutEvaluationOrderAddIso` in [SmallNormalFormAddEquiv.lean](../Surreal/Foundations/SmallNormalFormAddEquiv.lean); `cutEvaluation_ofFiniteMonomialForm`, `normalForm_finiteMonomialEvaluation` in [SmallNormalFormFiniteEvaluation.lean](../Surreal/Foundations/SmallNormalFormFiniteEvaluation.lean) | Every real-coefficient singleton evaluates to its actual monomial, using product-cut option gaps and reverse prefix simplicity. Nested support-length induction proves both prefix directions for arbitrary sums: the actual sum meets every formal center, and translated approximation invariants make the formal value realize the Conway sum cut. Native additive equivalences give subtraction and finite-sum laws. All finite monoid-algebra expressions agree with the earlier finite evaluation, including repeated exponents and cancellation. **Proved** without approximation-only uniqueness. Build and axiom audit pass. |
| Multiplication and ordered field normal-form bridge in `found:eq:normalform`, `found:sub:bridge` | `Surreal.Foundations.SmallNormalForm.exists_add_eq_of_mem_support_mul`, `trunc_product_frontier`, `coeff_product_frontier` in [SmallNormalFormProductFrontier.lean](../Surreal/Foundations/SmallNormalFormProductFrontier.lean); `cutEvaluation_mul` in [SmallNormalFormMultiplication.lean](../Surreal/Foundations/SmallNormalFormMultiplication.lean); `cutEvaluationRingHom`, `cutEvaluationRingEquiv`, `cutEvaluationOrderRingIso`, inverse/division/power/rational-cast laws and their extraction counterparts in [SmallNormalFormFieldEquiv.lean](../Surreal/Foundations/SmallNormalFormFieldEquiv.lean) | Each supported product exponent is a sum of supported factor exponents. Their earlier truncations determine the strictly earlier product, while the product of the remaining tails has the prescribed leading coefficient. Actual-birthday induction identifies earlier products and controls the full product's residual at every supported exponent. Canonical product-cut options, pulled back by extraction, prove the opposite prefix direction. Thus evaluation is an ordered field isomorphism between the small formal Hahn field and the actual sign field. **Proved** on arbitrary lower-universe-small supports, with zero cases retained. Small real strong sums are proved below; complex strong sums and univariate formal evaluation are proved above; the remaining analytic-operation correspondences and universe coherence remain separate obligations. Build and axiom audit pass. |
| Formal and actual workspace embeddings in `found:thm:workspace` | `Surreal.Foundations.SmallNormalForm.ofHahn`, `hahnGrowthMap`, `hahnEmbedding`, `coeff_hahnEmbedding`, `support_hahnEmbedding`, `hahnEmbedding_single`, `hahnEmbedding_injective` in [SmallNormalFormHahnEmbedding.lean](../Surreal/Foundations/SmallNormalFormHahnEmbedding.lean); `Surreal.Foundations.SignSequence.hahnEmbedding`, `normalForm_hahnEmbedding`, `hahnEmbedding_single`, `hahnEmbedding_injective`, `hahnOrderRingHom` in [SignSequenceHahnEmbedding.lean](../Surreal/Foundations/SignSequenceHahnEmbedding.lean) | A strictly increasing additive map from any lower-universe-small ordered exponent group to the actual sign field embeds its entire real Hahn field into the small formal field. Negating valuation exponents gives growth exponents, retaining exactly the transported support and recovering every coefficient. Composition with the proved field equivalence gives an injective actual evaluation preserving native lexicographic order and real monomials. **Proved** for these clauses; small real strong-sum compatibility is proved below; complex strong sums and univariate formal evaluation are proved above; recentered complex univariate lifting is proved above; its remaining analytic-operation correspondences are pending. Build and axiom audit pass. |
| Small-family and polynomial localization in `found:thm:workspace` | `Surreal.Foundations.SmallNormalForm.hahnPreimage`, `hahnEmbedding_hahnPreimage`, `familyWorkspaceEmbedding`, `familyHahnPreimage`, `familyWorkspaceEmbedding_preimage`, `exists_polynomial_hahn_preimage` in [SmallNormalFormWorkspace.lean](../Surreal/Foundations/SmallNormalFormWorkspace.lean) | Coefficient pullback recovers a form whenever its support lies in the negative exponent image. The rational span of a small family's support union is small and divisible, giving one injective Hahn embedding and exact preimages for every member. Polynomial coefficient descent follows from Mathlib's lifts API. **Proved** for formal families, with the actual ordered field equivalence available; small real strong sums and exponent-workspace coherence are proved below. Build and axiom audit pass. |
| Actual real closedness in `found:sub:package` and the real-field part of `found:thm:workspace` | `Surreal.Foundations.SmallNormalForm.exists_isRoot_of_odd_natDegree`, `isSquare_of_nonneg`, `smallNormalFormIsRealClosed` in [SmallNormalFormRealClosed.lean](../Surreal/Foundations/SmallNormalFormRealClosed.lean); `Surreal.Foundations.SignSequence.exists_isRoot_of_odd_natDegree`, `signSequenceIsRealClosed` in [SignSequenceRealClosed.lean](../Surreal/Foundations/SignSequenceRealClosed.lean) | Every polynomial descends to a small divisible real Hahn workspace. Injectivity preserves its degree, so the proved workspace odd-degree root theorem transfers to the formal field and through the field equivalence to actual sign surreals. Independently constructed nonnegative genetic square roots supply the other real-closedness premise. **Proved** unconditionally for both fields, without assuming either target real closed. Surcomplex algebraic closedness is proved below. Build and axiom audit pass. |




| `found:prop:allcuts` | `Surreal.Foundations.noUniversalStrictBound`, `noUnrestrictedStrictBounds`, `noUnrestrictedUpperBounds`, `noUnrestrictedCuts` in [SizeObstructions.lean](../Surreal/Foundations/SizeObstructions.lean) | Full unrestricted-bound and two-sided-cut contradiction for an arbitrary irreflexive relation. **Proved**; integrated build and axiom audit pass. |
| `found:sub:cutdata` | `Surreal.Foundations.SmallCutData`, `SmallCutData.IsRealizedBy`, `HasSmallCutFillers`, `HasSmallStrictUpperBounds` | Size-aware data and explicit abstract properties. Reindexing, the small-set interface, and the constructed sign-carrier model are mapped below. |
| `found:lem:bounds` | `Surreal.Foundations.HasSmallCutFillers.hasSmallStrictUpperBounds`, `HasSmallCutFillers.exists_strict_lower_bound`, `HasSmallCutFillers.exists_strict_lower_bound_above`, `HasSmallStrictUpperBounds.exists_bound_of_small_set` | Upper/lower/positive-lower bounds conditional on a proved small-cut-filler property. The property and the ordered-field structure are now proved for the sign carrier below. |
| `found:prop:universecut` | `Surreal.Foundations.not_small_of_small_strict_upper_bounds`, `not_small_of_small_cut_fillers` | The abstract non-smallness implication using Mathlib `Small`. The explicit relative-universe application is proved below on the same sign carrier whose ordered-field structure is now constructed. |
| `found:sub:properness`, `found:prop:proper`, birthday-bounded fragment assertion | `Surreal.Foundations.SignSequence`, `ofSigns`, `birthdays_bounded`, `small_bounded`, `not_small` in [SignSequence.lean](../Surreal/Foundations/SignSequence.lean) | A concrete carrier in `Type (u+1)` has an ordinal birthday in `Ordinal.{u}` and a zero-extended two-sign sequence. Arbitrary ordinal-length Boolean sign data construct elements. Every `u`-small family has strictly bounded birthdays, and every fixed birthday fragment (even with a non-strict bound) is `u`-small. The whole carrier is not `u`-small because its birthday map is onto all `u`-ordinals. This is the precise relative-universe properness assertion, not a set-theoretic proper class inside Lean. **Proved** for the constructed sign carrier; build and axiom audit pass. |
| Linear order, ordinal embedding, prefix simplicity and option-size clauses of `found:sub:signs`; `found:rem:simplicity` | `Surreal.Foundations.SignSequence.lt_iff`, `ordinalOrderEmbedding`, `IsPrefix`, `simpler_wellFounded`, `truncate`, `small_leftIndex`, `small_rightIndex`, `canonicalCut`, `canonicalCut_realized`, `neg_lt_neg_iff`, `birthday_precedence_not_prefix` in [SignSequence.lean](../Surreal/Foundations/SignSequence.lean) | Numerical order is Mathlib's lexicographic first disagreement with `-1 < termination < 1`. Prefix simplicity is separately well-founded by birthday; an explicit one-plus/two-minus example refutes the converse from birthday precedence. All-plus signs embed ordinals as an order embedding, with no claim about ordinary ordinal arithmetic. Sign reversal reverses numerical order. Canonical left/right options are the truncations before plus/minus signs, with lower-universe indices and a proved separator. Field arithmetic and arbitrary small-cut filling are not assumed. **Proved** for the sign carrier; build and axiom audit pass. |
| Simplest-separator clause of `found:sub:signs` | `Surreal.Foundations.SignSequence.isPrefix_of_separates_options`, `canonicalCut_isPrefix`, `canonicalCut_simplest` in [SignSequenceOptions.lean](../Surreal/Foundations/SignSequenceOptions.lean) | Every separator of the actual canonical small option families extends the original sequence. Thus the sequence is the unique separator of minimum birthday, including the empty sequence. The proof proceeds by well-founded induction over sign positions and uses the numerical truncation comparisons. This concerns canonical cuts; filling arbitrary small separated families and the resulting cut operation are mapped below. **Proved** for the sign carrier; build and axiom audit pass. |
| Upper-bound clause of `found:lem:bounds` on the constructed sign carrier | `Surreal.Foundations.SignSequence.lt_ofOrdinal_of_birthday_lt`, `small_strict_upper_bounds` in [SignSequence.lean](../Surreal/Foundations/SignSequence.lean) | An all-plus sequence of greater birthday bounds a given sequence numerically. Birthday bounds therefore prove the existing `HasSmallStrictUpperBounds` property for the actual carrier, without postulating general cut fillers. The other cut-based bounds and the ordered-field structure on the same carrier are mapped below. **Proved**; build and axiom audit pass. |
| `found:sub:cutdata`, indexed/predicate interface and reindexing assertion | `Surreal.Foundations.SmallCutData.reindex`, `reindex_isRealizedBy_iff`, `ofSmallSets`, `ofSmallSets_isRealizedBy_iff`, `HasSmallCutFillers.exists_separator_of_small_sets` in [SmallCutData.lean](../Surreal/Foundations/SmallCutData.lean) | Reindexing by equivalences preserves exactly the separator predicate. Two predicate-based option sets give lower-universe indexed cut data when both element types carry explicit `Small` witnesses. The separator equivalence is proved in both directions. This interface introduces no filler axiom. **Proved**; build and axiom audit pass. |
| Recursive comparison formula `found:eq:comparison` on canonical signs | `Surreal.Foundations.SignSequence.le_iff_options_lt`, `lt_iff_exists_option`, `le_iff_canonicalCut` in [SignSequenceComparison.lean](../Surreal/Foundations/SignSequenceComparison.lean) | Numerical comparison is equivalent to the Conway rule using canonical left options of the first number and right options of the second. Strict comparison has an option witness. The lower-universe canonical-cut version is included. This is a theorem for the extensional sign carrier, not a construction or quotient of raw games. **Proved**; build and axiom audit pass. |
| Simplest-number uniqueness in `found:sub:choice` and `found:sub:package` | `Surreal.Foundations.SignSequence.isPrefix_of_minimum_birthday`, `existsUnique_prefix_of_ordConnected`, `existsUnique_minimum_birthday_of_ordConnected`, `existsUnique_simplest_separator` in [SignSequenceSimplicity.lean](../Surreal/Foundations/SignSequenceSimplicity.lean) | Every nonempty order-convex set has a unique minimum-birthday element, which is a prefix of all its members. Separators form such a convex set. The simplicity theorem requires separator existence; that independent construction follows below. Unrestricted predicates occur here only with nonempty convexity, not as unrestricted cut inputs. **Proved**; build and axiom audit pass. |
| Small-cut construction and rank bound in `found:sub:signs`, `found:sub:cutdata`, `found:sub:package` | `Surreal.Foundations.SignSequence.exists_cut_separator_of_birthday_lt`, `small_cut_fillers` in [SignSequenceCut.lean](../Surreal/Foundations/SignSequenceCut.lean); `cut`, `cut_realizes`, `cut_isPrefix`, `cut_eq_iff`, `birthday_cut_le_iSup`, `cut_canonicalCut`, `cut_congr`, `cut_reindex` in [SignSequenceCutOperation.lean](../Surreal/Foundations/SignSequenceCutOperation.lean) | A fixed-length Boolean lexicographic complete lattice constructs a separator at any ordinal birthday strictly bounding all option birthdays, including limit bounds and empty cuts. Ordinal well-foundedness then selects the unique simplest separator. Its birthday is bounded by the small supremum of successor option birthdays, and it is a prefix of every separator. Canonical options reconstruct the original number; equal separator predicates and reindexing preserve the value. All cut indices remain in `Type u` while the carrier is in `Type (u+1)`. No unrestricted cut axiom or field structure is used. **Proved** for the concrete sign carrier; build and axiom audit pass. |
| `found:eq:negcut`; remaining bound clauses of `found:lem:bounds` | `Surreal.Foundations.SignSequence.negateCut`, `cut_negateCut`, `exists_strict_lower_bound`, `exists_positive_lower_bound`, `exists_separator_of_small_sets` in [SignSequenceCutOperation.lean](../Surreal/Foundations/SignSequenceCutOperation.lean) | Swapping and negating the option families makes the actual simplest cut value equal to the sign reversal of the original value. Small families have lower bounds and positive families have positive strict lower bounds, including empty families. Small predicate-based cuts are also filled. Numerical density and absence of endpoints are proved instances. The arithmetic construction, its recursive addition law and the ordered-field structure are mapped below. **Proved** for the sign carrier; build and axiom audit pass. |
| Cut-based generalization following `found:prop:incomplete`, and its order-theoretic counterexample | `Surreal.Foundations.SignSequence.exists_smaller_upper_bound`, `no_isLUB_of_no_greatest`, `finite_ordinals_bounded_without_supremum` in [SignSequenceBounds.lean](../Surreal/Foundations/SignSequenceBounds.lean) | Every proposed upper bound of a small set without a greatest member has a strictly smaller upper bound. Embedded finite ordinals form a nonempty bounded small set with no supremum. Thus the constructed numerical order is not Dedekind complete. Native natural/integer casts and the subtraction-by-one proof are constructed below. The alternative halving proof is provided below using the constructed field. **Proved** for the order assertion; build and axiom audit pass. |
| `found:eq:comparison` for arbitrary small presentations and its option-domination consequences | `Surreal.Foundations.SignSequence.cut_le_cut_iff`, `cut_le_iff`, `le_cut_iff`, `cut_lt_cut_iff`, `cut_le_cut_of_options`, `leftOption_cut_le`, `le_rightOption_cut` in [SignSequenceCutComparison.lean](../Surreal/Foundations/SignSequenceCutComparison.lean) | The comparison rule holds for arbitrary small separated cut presentations. Every canonical left option is dominated by an original left option, and every canonical right option is above an original right option. Only these directions are asserted; redundant presentation options need not be canonical. The proof uses separator simplicity, not a supremum interpretation of cuts. **Proved**; build and axiom audit pass. |
| `found:sub:recursionmeasure`; nested canonical option prerequisite for `found:eq:addcut` | `Surreal.Foundations.SignSequence.PairSimpler`, `pairSimpler_wellFounded`, the four canonical option decrease lemmas, `numerical_not_wellFounded`, `maximum_birthday_not_decreasing`, `ordinal_sum_birthday_not_decreasing` in [SignSequenceRecursion.lean](../Surreal/Foundations/SignSequenceRecursion.lean); `truncate_truncate`, `IsPrefix.truncate_eq`, `left_right_option_nested` in [SignSequenceTruncation.lean](../Surreal/Foundations/SignSequenceTruncation.lean) | Mathlib's game-addition relation supplies a checked well-founded relation for decreasing one input at a time. Canonical opposite options are nested truncations. Explicit sign sequences show that numerical order is not well founded and that maximum birthday and ordinary ordinal addition fail to decrease in the proposed cases. This proves the relation-based recursion route. A separate natural-sum measure proof is mapped below; the raw multiplication termination argument remains in the reused game library. **Proved**; build and axiom audit pass. |
| `found:eq:addcut`, additive ordered-group obligations following it, and additive portion of `found:sub:package` | `Surreal.Foundations.SignSequence.add`, `add_options_separated`, `addCut`, `add_eq_cut`, `addCut_realizes_iff`, `add_comm`, `add_zero`, `zero_add`, `add_right_strictMono`, `add_left_strictMono`, cancellation laws in [SignSequenceAddition.lean](../Surreal/Foundations/SignSequenceAddition.lean); `sumCut`, `cut_sumCut`, `add_assoc` in [SignSequenceAddAssociative.lean](../Surreal/Foundations/SignSequenceAddAssociative.lean); `add_neg_cancel`, `neg_add_cancel` in [SignSequenceAddInverse.lean](../Surreal/Foundations/SignSequenceAddInverse.lean); native group/order instances in [SignSequenceAddGroup.lean](../Surreal/Foundations/SignSequenceAddGroup.lean) | Actual Conway addition is defined by native well-founded pair recursion. The internal fallback is proved unreachable: all recursive option families are small and separated, using nested canonical options and earlier recursive bounds. The operation obeys the simplest-cut equation, including arbitrary small presentations of both summands. Commutativity, zero, strict translation, cancellation, associativity and inverses are independently proved before assembling `AddCommGroup` and `IsOrderedAddMonoid`; the inverse is the existing sign reversal and the order is the existing numerical order. Multiplication and field inverses are transported through the proved arithmetic equivalence below. Real closedness and the ordered field normal-form bridge are proved above. **Proved** for the concrete additive sign carrier; build and axiom audit pass. |
| Integer embedding in `found:sub:package`; native natural-number and subtraction clauses of `found:prop:incomplete` | `Surreal.Foundations.SignSequence.natCast_eq_ofOrdinal`, `intCast_negSucc_eq_neg_ofOrdinal`, `birthday_natCast`, `integerAddHom`, `integerOrderEmbedding`, `range_natCast_eq_finite_ordinals`, `natCast_lt_omega0`, `sub_one_mem_upperBounds_natCast`, `natCast_range_no_isLUB`, `natural_numbers_bounded_without_supremum` in [SignSequenceIntegers.lean](../Surreal/Foundations/SignSequenceIntegers.lean) | The one-plus sequence and actual Conway additive group give native `AddCommGroupWithOne` and `CharZero` instances. Cut induction proves that natural casts are precisely finite all-plus sequences; negative integers are the corresponding sign reversals. Integer casts preserve addition and strictly preserve order. The all-plus sequence of length omega strictly bounds the natural range, and subtracting one from any upper bound gives a smaller upper bound, proving there is no supremum. No multiplication, rational embedding or Archimedean property is assumed. The source's alternative halving argument is proved below in the ordered field. **Proved** for the concrete additive sign carrier; build and axiom audit pass. |
| Closed/discrete-subset and convergent-net clauses of `found:thm:discrete`; no-isolated-points sharpness | `Surreal.Foundations.SignSequence.exists_Ioo_inter_subset_singleton`, `isClosed_of_small`, `isDiscrete_of_small`, `discreteTopology_of_small`, `tendsto_nhds_iff_eventually_eq_of_small_range`, `tendsto_nhds_iff_eventually_eq`, `punctured_nhds_neBot`, `not_discreteTopology` in [SignSequenceTopology.lean](../Surreal/Foundations/SignSequenceTopology.lean) | Native order topology on the concrete carrier has closed/discrete lower-universe-small subsets. Small range suffices for convergence along any filter to be equivalent to eventual equality; small index types are a corollary. The whole carrier is not discrete and has no isolated points. Smallness is retained on the subset/range/index type, never assumed for unrestricted predicates. The self-valued absolute-ball interpretation is proved below. The surcomplex product topology and its squared-radius and actual modulus bases are constructed below. **Proved** for the real sign carrier; build and axiom audit pass. |
| Cauchy-net clause of `found:thm:discrete`, additive uniformity and real-carrier specialization | `Surreal.Foundations.HasSmallCutFillers.exists_pos_lt_abs_sub`, `exists_entourage_eq_on_small_set`, `eventually_constant_of_cauchy_small_range`, `eventually_constant_of_cauchy`, `cauchy_map_iff_eventually_constant` in [SmallCauchy.lean](../Surreal/Foundations/SmallCauchy.lean); concrete uniformity and specializations in [SignSequenceUniformity.lean](../Surreal/Foundations/SignSequenceUniformity.lean) | For ordered additive groups with compatible order topology and native group uniformity, small cut filling gives one positive bound below all nonzero pairwise absolute differences of a small range. An actual entourage therefore forces equality, and native `Cauchy (map f l)` implies eventual constancy along an arbitrary filter; the iff includes `NeBot l`. The constructed sign group's native uniformity preserves its order topology definitionally and has self-valued absolute-difference neighborhood/entourage bases, so the Cauchy conclusion is instantiated on the concrete carrier. No real-valued metric or completeness assumption is used. The corresponding surcomplex uniformity and modulus bridge are proved below. **Proved** for the real additive sign carrier; build and axiom audit pass. |
| `found:ex:largerindex` | `Surreal.Foundations.SignSequence.PositiveNetIndex`, `positiveNet`, `positiveNet_tendsto_zero`, `positiveNet_cauchy`, `positiveNet_not_eventually_zero`, `positiveNet_not_eventually_constant`, `positiveNetIndex_not_small` in [SignSequenceLargeNet.lean](../Surreal/Foundations/SignSequenceLargeNet.lean) | All positive sign sequences, with reverse numerical order, index a nontrivial directed net which converges to zero in the native order topology and is Cauchy in the additive uniformity. Every term is positive and the net is never eventually constant. Its index type is explicitly proved not `Small.{u}`, demonstrating that the small-index hypotheses cannot be removed. Density supplies a smaller positive radius without requiring division by two. The surcomplex inclusion and its larger-index net are constructed below. **Proved** for the concrete real sign carrier; build and axiom audit pass. |
| Comparison and canonical-option part of the sign/game bridge in `found:sub:signs` and `found:sub:twotracks` | `Surreal.Foundations.SignSequence.canonicalGameGraph`, `canonicalGameGraph_move_simpler`, `toIGame`, `leftMoves_toIGame`, `rightMoves_toIGame`, `toIGame_eq`, `toIGame_le_iff`, `toIGame_lt_iff`, `toIGame_equiv_iff`, `numeric_toIGame`, `toSurrealOrderEmbedding` in [SignSequenceGames.lean](../Surreal/Foundations/SignSequenceGames.lean) | Canonical sign options are small move sets decreasing prefix simplicity, so upstream `GameGraph.toIGame` constructs their raw game. Paired well-founded induction proves both comparison orientations before numericity is established. Game equivalence identifies exactly equal sign sequences, and the numeric-game quotient receives an explicit order embedding. This preserves the actual canonical options and numerical order. Arbitrary-cut preservation, surjectivity and arithmetic preservation are proved below before transferring field operations. **Prerequisites proved**; build and axiom audit pass. |
| Zero and unit compatibility in the sign/game bridge | `Surreal.Foundations.SignSequence.toIGame_zero`, `toIGame_one`, `toSurreal_zero`, `toSurreal_one` in [SignSequenceGameConstants.lean](../Surreal/Foundations/SignSequenceGameConstants.lean) | The empty and one-plus sequences give literal equality with the upstream raw games zero and one, hence also preserve these constants in the numeric-game quotient. These are the already constructed sign zero and additive unit. Addition compatibility and transport of multiplication are proved below. **Proved** for these bridge constants; build and axiom audit pass. |
| Numeric-game small-cut route in `found:sub:cutdata`; `found:eq:comparison` | `Surreal.Foundations.gameCut`, `left_lt_gameCut`, `gameCut_lt_right`, `gameCut_realizes`, `game_hasSmallCutFillers`, `gameCut_le_gameCut_iff`, `gameCut_lt_gameCut_iff`, `numericGameCut`, `gameCut_numericGameCut` in [GameCuts.lean](../Surreal/Foundations/GameCuts.lean) | Lower-universe indexed separated option families define cuts in the reused numeric-game quotient. Their values separate the options and obey both recursive comparison formulas. Reindexing a numeric game's small move sets by `Shrink` and mapping them into the quotient reconstructs its original quotient value. This establishes the native game-side interface without assuming a sign equivalence or a canonical quotient representative. **Proved** for the numeric-game carrier; build and axiom audit pass. |
| Order and arbitrary-cut equivalence in `found:sub:signs` and the game/sign route of `found:sub:twotracks` | `Surreal.Foundations.SignSequence.toSurrealCut`, `gameCut_toSurrealCut_canonical`, `toSurreal_cut`, `exists_toSurreal_eq_mk`, `toSurreal_surjective`, `toSurrealOrderIso` in [SignSequenceGameEquiv.lean](../Surreal/Foundations/SignSequenceGameEquiv.lean) | The explicit embedding preserves every small separated cut, including arbitrary presentations and duplicate options. Induction over numeric-game moves constructs a sign preimage for every numeric game using lower-universe indexed option cuts. Quotient induction then gives surjectivity and an actual order isomorphism in the same universe. The proof makes no whole-carrier smallness assumption and does not identify arbitrary separators with cut values. Compatibility with existing addition and transport of field operations are proved below; birthday/simplicity correspondence and the Hahn bridge remain separate. **Proved** for the order and cut equivalence; build and axiom audit pass. |
| Existing-addition compatibility in `found:eq:addcut` and the game/sign bridge | `Surreal.Foundations.SignSequence.toSurreal_add`, `toSurreal_neg`, `toSurreal_sub`, `toSurrealAddHom`, `toSurrealAddEquiv`, `toSurrealOrderAddIso` in [SignSequenceGameAddition.lean](../Surreal/Foundations/SignSequenceGameAddition.lean) | Pair recursion proves that the order/cut equivalence preserves the independently constructed Conway addition by matching all four canonical option families. Negation and subtraction then follow from the existing additive-group laws. The resulting ordered additive equivalence retains the original operations; it does not redefine addition by transport. **Proved**; build and axiom audit pass. |
| Ordered-field structure in `found:sub:package` and arithmetic field laws following `found:eq:mulcut` | `Surreal.Foundations.SignSequence.mul`, `inv`, `signSequenceCommRing`, `signSequenceIsStrictOrderedRing`, `signSequenceField`, `toSurreal_mul`, `toSurreal_inv`, `toSurreal_div`, `toSurrealRingEquiv` in [SignSequenceField.lean](../Surreal/Foundations/SignSequenceField.lean) | The explicit equivalence transports the reused numeric-game multiplication and total inverse onto the sign carrier. Ring and field laws are proved while retaining the existing additive group with one and numerical order; the same map is a field isomorphism. No new mathematical axioms or real-closedness premise are introduced. The native genetic product-cut equation is proved below; real closedness and the Hahn ordered field equivalence are proved above. **Proved** for the concrete ordered field; build and axiom audit pass. |
| `found:eq:mulcut` for canonical sign options | `Surreal.Foundations.SignSequence.mulOption`, `mul_sub_mulOption`, the four option-bound lemmas, `mulLeft`, `mulRight`, `mul_options_separated`, `mulCut`, `mulCut_realized`, `mul_eq_cut` in [SignSequenceMultiplication.lean](../Surreal/Foundations/SignSequenceMultiplication.lean) | The transported field product is exactly the simplest value of the genetic product cut. Left options pair left with left or right with right; right options pair opposite sides. The rectangle identity factors the difference from the product into two option gaps, proving every strict bound and separation. Shrinking the four product families keeps both cut indices in the lower universe. Exact equality follows by matching the upstream raw-game multiplication formula through the proved cut/arithmetic bridge, not by treating every separator as the cut value. The arbitrary-presentation formula is proved below. General multiplicative birthday bounds remain separate. **Proved** for the concrete sign field; build and axiom audit pass. |
| `found:eq:mulcut` for arbitrary small factor presentations | `Surreal.Foundations.SignSequence.productCut`, `productCut_realizes_iff`, `productCut_realized`, `productCut_realizes_mulCut`, `cut_productCut`, `productCut_isPrefix_of_realizes` in [SignSequenceProductCuts.lean](../Surreal/Foundations/SignSequenceProductCuts.lean) | Conway multiplication holds for any two small separated cut presentations, including redundant options. Monotonicity of the rectangle expression transfers canonical-option cofinality to the four product families. Mutual prefix simplicity identifies their cut with the existing field product; a separator is not assumed equal to the simplest value. Every cut index stays in the lower universe. **Proved**; build and axiom audit pass. |
| Rational embeddings and non-Archimedean scales; halving proof of `found:prop:incomplete` | `Surreal.Foundations.SignSequence.rationalRingHom`, `rationalOrderEmbedding`, `toSurreal_ratCast`, `ratCast_lt_omega0`, `not_archimedean`, `natCast_lt_half_of_mem_upperBounds`, `half_mem_upperBounds_natCast`, `natCast_range_no_isLUB_by_halving`, `inv_omega0_pos`, `inv_omega0_lt_one_div_natCast`, `inv_omega0_lt_ratCast` in [SignSequenceRationals.lean](../Surreal/Foundations/SignSequenceRationals.lean) | Native rational casts preserve the field and order and agree across the sign/game equivalence. The concrete all-plus omega dominates every rational and refutes the native Archimedean property. Its reciprocal is positive and below every positive rational; reciprocal-natural statements retain the positive-index guard. Any upper bound of the natural range can be halved to a strictly smaller upper bound, completing the second source argument. No real-closedness or Hahn identification is assumed. **Proved** for these concrete embeddings, scale and incompleteness assertions; build and axiom audit pass. |
| `found:rem:ordinals` | `Surreal.Foundations.SignSequence.toIGame_ofOrdinal`, `toSurreal_ofOrdinal`, `ofOrdinal_natural_add`, `ofOrdinal_natural_mul`, `naturalOrdinalRingHom`, `ofOrdinal_add_one`, `one_add_ofOrdinal_omega0`, `ofOrdinal_one_add_omega0_ne`, `not_ofOrdinal_preserves_ordinal_add` in [SignSequenceOrdinals.lean](../Surreal/Foundations/SignSequenceOrdinals.lean) | All-plus sign sequences agree literally with upstream ordinal raw games. Their arithmetic therefore agrees with the natural sum and product on the explicit `NatOrdinal` wrapper, which is an ordered semiring embedded into the sign field. Ordinary ordinal addition is kept separate: the field sum `1 + omega` is the successor of omega, while embedding the ordinary ordinal sum gives omega. No arithmetic instance on `Ordinal` is changed. **Proved**; build and axiom audit pass. |
| Ordinary-real coefficient embedding prerequisite for `found:eq:normalform` and `found:sub:hahnworkspace`; real-scale distinction in `found:sub:modulus` | `Surreal.Foundations.SignSequence.ofReal`, `realOrderEmbedding`, `toSurreal_ofReal`, arithmetic/cast compatibility, `ofReal_lt_omega0`, `omega0_not_mem_range_ofReal`, `inv_omega0_lt_ofReal`, `exists_pos_lt_all_pos_ofReal` in [SignSequenceReal.lean](../Surreal/Foundations/SignSequenceReal.lean) | The upstream dyadic Dedekind-cut embedding of ordinary reals composes with the proved sign/game field equivalence to give an actual ordered real-field embedding, compatible with natural, integer, rational and dyadic values. Omega exceeds every embedded real, and its positive reciprocal lies below every positive embedded real. This supplies the coefficient subfield and the explicit distinction between ordinary reals and surreal scales; it does not construct Hahn evaluation, a normal form, or a real-valued modulus. **Prerequisites proved**; build and axiom audit pass. |
| Actual real-coordinate standard part for `a:eq:st` | `Surreal.Foundations.SignSequence.IsFinite`, `IsInfinitesimal`, natural/real bound equivalences, `standardPartHom`, `standardPartHom_surjective`, `infinitesimalIdeal_eq_maximalIdeal`, `standardPartQuotientEquiv`, `existsUnique_real_infinitesimal_decomposition` in [SignSequenceStandardPart.lean](../Surreal/Foundations/SignSequenceStandardPart.lean) | Mathlib’s native Archimedean valuation ring on the actual ordered sign field has residue field `ℝ` through the constructed ordinary-real embedding. Finiteness means an absolute bound by some natural; infinitesimality means an absolute bound by every positive reciprocal natural, equivalently every positive ordinary real. Standard part is an ordered ring homomorphism on finite elements, with native maximal infinitesimal kernel and a unique real-plus-infinitesimal decomposition. Zero is included in the ideal; algebraic laws retain finite-domain guards. No Hahn coefficient identification is assumed. **Proved**; build and axiom audit pass. |
| Real-coordinate clopen and separation clauses of `a:prop:clopen` | `Surreal.Foundations.SignSequence.isClopen_setOf_isFinite`, `isClopen_setOf_isInfinitesimal`, `isClopen_monad`, `isClopen_affine_finite`, `isClopen_affine_infinitesimal`, `affine_infinitesimals_eq`, `exists_isClopen_separating`, `signSequenceTotallySeparatedSpace` in [SignSequenceStandardPartTopology.lean](../Surreal/Foundations/SignSequenceStandardPartTopology.lean) | A positive actual infinitesimal gives a neighborhood inside the infinitesimal additive subgroup, making it and the finite subgroup clopen. Every nonzero affine image is clopen, including monads centered at infinite elements. Scaled monads separate every pair of distinct sign-field elements, supplying native total separatedness and disconnectedness while retaining the existing topology. The full surcomplex proposition is proved below. **Proved** for these scalar clauses; build and axiom audit pass. |
| Actual monomial and leading-data prerequisites of `found:eq:normalform`, `found:sub:hahnworkspace` | `Surreal.Foundations.SignSequence.toSurrealOrderRingIso`, Archimedean comparison transport, `omegaPower`, its strict order and exponent laws, `leadingExponent`, `leadingCoeff`, `leadingCoeff_eq_standardPart`, `finite_div_omegaPower_iff`, `infinitesimal_div_omegaPower_iff`, `standardPart_div_omegaPower_ne_zero_iff` in [SignSequenceMonomials.lean](../Surreal/Foundations/SignSequenceMonomials.lean) | The pinned Conway omega-map and logarithm transport through the actual ordered field equivalence. A nonzero element has a unique leading growth exponent and nonzero real coefficient, with normalized finite part having nonzero standard part. Scaling by `omegaPower a` is finite exactly when the growth exponent is at most `a`, and has nonzero standard part exactly at equality. The exponent at zero is a total junk value, so comparison and multiplicative criteria retain their nonzero guards. The source convention is `t^a = omegaPower (-a)`. No infinite normal form or strong evaluation is asserted. **Prerequisites proved**; build and axiom audit pass. |
| Finite monomial-scaling prerequisite for `found:sub:realclosed` | `Surreal.Foundations.SignSequence.finite_div_omegaPower_pow_iff`, `standardPart_div_omegaPower_pow_ne_zero_iff`, `exists_monomial_normalization`, `exists_monomial_finite_scaling`, `exists_pos_coefficient_scaling`, `exists_lowerCoeff_monomial_normalization` in [SignSequencePolynomialScaling.lean](../Surreal/Foundations/SignSequencePolynomialScaling.lean) | Taking the maximum of finitely many nonzero coefficients’ leading exponents divided by positive natural weights gives an actual positive monomial scale. Every weighted coefficient is finite and at least one has nonzero real standard part. Weights `n-j` specialize the theorem to all lower coefficients of a monic degree-`n` polynomial. The finiteness-only result includes all-zero and empty families; the attained nonzero residue explicitly requires a nonzero coefficient. The polynomial change of variable and ordinary-real reduction factorization are constructed below; the infinite factor lift remains separate. **Prerequisite proved**; build and axiom audit pass. |
| Polynomial translation and real residue factorization prerequisites of `found:sub:realclosed` | `Surreal.FinitePolynomial.coeff_taylor_pred_natDegree`, `monicNormalize`, `depress`, `coeff_depress_pred_eq_zero`, explicit root/translation identities, `exists_monic_depressed` in [PolynomialDepression.lean](../Surreal/Algebra/PolynomialDepression.lean); `depressed_ne_linear_pow`, `real_monic_odd_exists_root`, `real_exists_coprime_monic_factors`, `real_depressed_odd_coprime_factorization` in [RealPolynomialFactors.lean](../Surreal/Algebra/RealPolynomialFactors.lean) | Leading-coefficient normalization and Taylor translation turn any nonzero positive-degree polynomial over a characteristic-zero field into a monic depressed polynomial of the same degree, with equivalent root existence. A nontrivial depressed odd-degree ordinary-real polynomial has coprime monic factors of positive degree, one of odd degree strictly below the original. The proof extracts the full multiplicity of a real root supplied by Mathlib’s real intermediate-value consequences and uses degree parity. It neither assumes nor proves surreal root existence. **Prerequisites proved**; build and axiom audit pass. |
| Actual polynomial scaling and standard-part reduction for `found:sub:realclosed` | `Surreal.Foundations.SignSequence.scalePolynomial`, coefficient and degree formulas, `scalePolynomial_monic`, `scalePolynomial_depressed`, `isRoot_scalePolynomial_iff`, `scalePolynomial_reconstruct`, `finitePolynomial`, `reducePolynomial`, `exists_scalePolynomial_finite`, `exists_monic_depressed_reduction` in [SignSequencePolynomialNormalization.lean](../Surreal/Foundations/SignSequencePolynomialNormalization.lean) | The actual transformation is `Q = C((t^n)⁻¹) * P.comp(C t * X)`, with lower coefficients `P_j / t^(n-j)` and explicit inverse transformation and root pullback. A monomial scale makes all coefficients finite. The resulting polynomial over the genuine finite-element ring reduces via standard part to an ordinary-real polynomial preserving monicity, degree and depression. For `P ≠ X^n`, a nonzero lower residue ensures the reduction is also not a pure monomial. Coprime factor lifting is proved in Hahn workspaces below, and actual surreal root existence follows from the proved workspace localization above. **Prerequisites proved**; build and axiom audit pass. |
| Complete finite preparation of the odd-degree-root induction in `found:sub:realclosed` | `Surreal.Foundations.SignSequence.scalePolynomial_depress_eq`, `isRoot_scalePolynomial_depress_iff`, `explicit_root_or_coprime_residue_preparation` in [SignSequenceRealClosedReduction.lean](../Surreal/Foundations/SignSequenceRealClosedReduction.lean) | Every monic odd-degree polynomial over the actual sign field either has the explicit root given by the negative depression shift, or admits a specified positive monomial scaling and translation whose finite standard-part reduction has coprime monic real factors. One factor has positive odd degree strictly below the original, and their degrees sum to the original degree. The exact transformed polynomial and affine root pullback are included. Lifting these residue factors inside the sign field remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Actual real-field valuation prerequisites of `a:eq:valuation` | `Surreal.Foundations.SignSequence.valuation`, `valuation_isEquiv_archimedean`, arithmetic/order formulas, `isFinite_iff_valuation_nonneg`, `isInfinitesimal_iff_valuation_pos`, `tMonomial`, `valuation_tMonomial`, `valuation_surjective`, `abs_lt_omegaPower_one_of_finite` in [SignSequenceValuation.lean](../Surreal/Foundations/SignSequenceValuation.lean) | Assigning zero infinity and nonzero elements minus their growth exponent gives a native additive valuation valued in `WithTop SignSequence`. It is equivalent to the native Archimedean valuation. The monomial convention is `t^a = omegaPower(-a)` and every surreal exponent occurs; no value-group truncation is imposed. Finiteness and infinitesimality agree with the already proved predicates. Identification with least support exponents for the full Hahn embedding is proved above. **Proved** for the actual valuation structure and these formulas; build and axiom audit pass. |
| Birthday correspondence and minimal-representative clauses in `found:sub:signs` and `found:sub:package` | `Surreal.Foundations.SignSequence.birthday_toIGame`, `numericGameSignCut`, `cut_numericGameSignCut`, `birthday_orderIso_symm_mk_le`, `birthday_le_of_toSurreal_eq_mk`, `toIGame_birthday_minimal` in [SignSequenceGameBirthday.lean](../Surreal/Foundations/SignSequenceGameBirthday.lean) | The canonical raw game's birthday is exactly the ordinal sign length. Passing from any numeric game to its sign representative never increases birthday, so the canonical game attains the minimum among all numeric representatives. The proof recursively uses small move cuts and the existing cut birthday bound. It does not identify birthday precedence with prefix simplicity. Quotient-level birthday APIs and arithmetic birthday estimates remain separate. **Proved** for the canonical and minimum-birthday assertions; build and axiom audit pass. |
| `lem:add` in the Laurent-birthday report; `found:eq:natsum` and `found:sub:recursionmeasure` | `Surreal.Foundations.SignSequence.birthday_add_le_natural`, `birthday_sub_le_natural`, `birthday_finset_sum_le`, `birthday_nsmul_le`, `pairBirthday`, `pairBirthday_lt_of_pairSimpler`, `pairSimpler_wellFounded_by_birthday`, `birthday_add_ofOrdinal`, `birthday_mul_ofOrdinal` in [SignSequenceBirthdayArithmetic.lean](../Surreal/Foundations/SignSequenceBirthdayArithmetic.lean), together with `birthday_neg` | Canonicalization of the raw game sum proves the natural-sum bound for actual sign addition, including arbitrary finite sums and finite multiples. Negation preserves sign length. The natural-sum measure strictly decreases when either coordinate becomes a proper sign prefix, giving a separate measured well-foundedness proof. On all-plus ordinal signs, both additive and multiplicative birthday bounds are equalities. Natural operations are explicitly those of `NatOrdinal`; this does not prove the general birthday-product conjecture. **Proved** for the full additive lemma and these measure/special-case assertions; build and axiom audit pass. |
| Finite-birthday cutoff in `found:sub:cutoffs` | `Surreal.Foundations.SignSequence.short_toIGame_iff`, `birthday_dyadicCast_lt_omega0`, `birthday_lt_omega0_iff_dyadic`, `dyadicRingHom`, `finiteBirthdaySubring`, `mem_finiteBirthdaySubring`, `birthday_add_lt_omega0`, `birthday_mul_lt_omega0`, `three_finite_birthday_inverse_not`, `not_exists_subfield_finite_birthday` in [SignSequenceDyadics.lean](../Surreal/Foundations/SignSequenceDyadics.lean) | A sign sequence has birthday below omega exactly when it is the embedded value of a dyadic rational. This uses the proved canonical birthday bridge and the upstream short numeric-game classification. These elements form a subring under the actual field operations. Three has finite birthday, while its reciprocal does not, so no ambient subfield has exactly this carrier. The exact finite dyadic birthday formula is proved below. **Proved** for the finite-cutoff classification and closure obstruction; build and axiom audit pass. |
| Non-dyadic real birthday assertions preceding `eq:realbirth` and `eq:dyadic-birthday`; prerequisite for `lem:realproduct` | `Surreal.Foundations.SignSequence.real_toIGame_birthday_le_omega0`, `birthday_ofReal_le_omega0`, `birthday_ofReal_lt_omega0_iff`, `birthday_ofReal_eq_omega0_of_not_dyadic`, `birthday_ofReal_eq_omega0_iff`, `birthday_one_third_eq_omega0` in [SignSequenceRealBirthday.lean](../Surreal/Foundations/SignSequenceRealBirthday.lean) | Every ordinary real has sign birthday at most omega: its raw dyadic Dedekind cut has short options, and canonicalization never increases birthday. It has finite birthday exactly when it is dyadic, and birthday exactly omega otherwise, including the explicit one-third example. These are concrete assertions about the constructed real embedding. The exact finite dyadic birthday formula and full real-product birthday inequality are proved below. **Proved** for the stated bounds and characterizations; build and axiom audit pass. |
| Exact finite formulas `eq:realbirth` and `eq:dyadic-birthday` | `Surreal.Foundations.DyadicBirthdayArithmetic.height`, `height_of_den_eq_one`, `max_height_lower_upper_add_one` in [DyadicBirthdayArithmetic.lean](../Surreal/Foundations/DyadicBirthdayArithmetic.lean); `SignSequence.birthday_dyadicCast_eq_game`, `birthday_dyadicCast_eq_max`, `dyadic_game_birthday_minimal`, `birthday_intCast`, `birthday_dyadicCast_formula`, `birthday_dyadicCast_of_den_eq_two_pow`, `birthday_ofReal_dyadic_formula` in [SignSequenceDyadicBirthday.lean](../Surreal/Foundations/SignSequenceDyadicBirthday.lean) | A dyadic with reduced denominator `2^k` has actual sign birthday `ceil(abs(q)) + k`, including negative values and zero. The arithmetic recurrence uses the reduced denominator and natural ceiling of the absolute rational value. Neighbor-cut prefix arguments and denominator induction independently prove that the native dyadic game has exactly the canonical sign birthday; equivalence alone is not used to identify raw birthdays. Proven arithmetic helpers are adapted with attribution from the recorded upstream revision, without importing its incomplete birthday module or enlarging the vendored dependency closure. **Proved** for the full formulas and the constructed ordinary-real embedding; build and axiom audit pass. |
| `lem:realproduct` in the Laurent-birthday report | `Surreal.Foundations.DyadicBirthdayArithmetic.log_den_mul_le`, `ceil_abs_mul_le`, `height_mul_le` in [DyadicBirthdayProduct.lean](../Surreal/Foundations/DyadicBirthdayProduct.lean); `SignSequence.birthday_dyadicCast_mul_le_natural`, `birthday_ofReal_mul_le_natural`, `birthday_ofReal_mul_le` in [SignSequenceRealProductBirthday.lean](../Surreal/Foundations/SignSequenceRealProductBirthday.lean) | For every pair of ordinary reals embedded in the actual sign field, the product birthday is at most the Hessenberg natural product of their birthdays. The dyadic case uses the exact finite formula, submultiplicativity of the absolute-value ceiling, and subadditivity of the reduced-denominator exponent. A nondyadic factor has birthday omega, and the real product has birthday at most omega. Zero factors are handled separately. This proves the entire real-scalar lemma, not the conjecture for arbitrary surreal factors. **Proved**; build and axiom audit pass. |
| `found:eq:pairmul`, `found:eq:conj`, `found:eq:pairinv`; part of `found:prop:complex` | `Surreal.Complexify`, `Complexify.mul_re`, `mul_im`, `I_sq`, `conj_conj`, `conj_mul`, `noRootNegOne`, `inv_eq`, `inv_re`, `inv_im` in [Complexify.lean](../Surreal/Algebra/Complexify.lean) | Mathlib quadratic algebra and its field instance over an arbitrary ordered field. The concrete sign-field specialization is proved below; actual algebraic closedness is proved below. **Prerequisites proved**; build and axiom audit pass. |
| Concrete pair field in `found:sub:pairs`; `found:eq:pairadd`, `found:eq:pairmul`, `found:eq:conj`, `found:eq:pairinv`; field and carrier clauses of `found:prop:complex` | `Surreal.Surcomplex`, `Surcomplex.ofReal`, `ofReal_injective`, `I_sq`, `add_eq`, `mul_eq`, `conj`, `conj_eq`, `conj_conj`, `re_add_im_mul_I`, `normSq_pos`, `normSq_mul`, `mul_conj`, `inv_eq`, `finrank_eq_two`, `not_small` in [Surcomplex/Basic.lean](../Surreal/Surcomplex/Basic.lean) | The concrete surcomplex carrier is the existing quadratic algebra over the constructed sign field, inheriting its proved field instance. Its coordinate addition, multiplication, conjugation and inverse formulas are instantiated without additional premises; the inverse denominator is positive for every nonzero pair. Norm squares take values in the sign field, and every pair decomposes as real plus imaginary parts. The extension has dimension two and is not lower-universe-small because its injective real axis already contains the entire sign carrier. Its fine topology and actual surreal-valued modulus are constructed below; actual algebraic closedness is proved below. **Proved** for these concrete field, coordinate and size clauses; build and axiom audit pass. |
| Surcomplex clauses of `found:thm:discrete`, fine-ball topology and no-isolated-points sharpness in `found:sub:discrete` | `Surreal.Surcomplex.coordinateUniformEquiv`, `surcomplexIsUniformAddGroup`, `fineBall`, `isOpen_fineBall`, `nhds_hasBasis_fineBall`, `uniformity_hasBasis_normSq_sub`, `isClosed_of_small`, `isDiscrete_of_small`, `tendsto_nhds_iff_eventually_eq_of_small_range`, `eventually_constant_of_cauchy_small_range`, `cauchy_map_iff_eventually_constant`, `punctured_nhds_neBot`, `not_discreteTopology` in [Surcomplex/FineTopology.lean](../Surreal/Surcomplex/FineTopology.lean) | The actual pair field carries the product of the native sign uniformities, compatible with its existing addition. Positive surreal squared-radius balls `normSq (z-a) < r²` give exactly its neighborhood and entourage bases. Every lower-universe-small subset is closed and discrete. Small-range convergent nets are eventually their limits, and small-range Cauchy nets are eventually an attained value; small index types imply these hypotheses. The Cauchy iff retains nontriviality of the filter. Every ball contains the distinct point `a + r/2` along the real axis, so the full carrier has no isolated points. No real-valued metric, square-root or real-closedness premise is used. **Proved** in squared-radius form; the actual modulus identification is proved below. Build and axiom audit pass. |
| Fine-topological compatibility of `found:sub:pairs`; surcomplex form of `found:ex:largerindex` | `Surreal.Surcomplex.surcomplexT2Space`, `continuous_mul_coordinates`, `continuousAt_inv_of_ne_zero`, `surcomplexIsTopologicalDivisionRing`, `conjUniformEquiv`, `conjHomeomorph`, `uniformContinuous_ofReal`, `positiveRealAxisNet_tendsto_zero`, `positiveRealAxisNet_cauchy`, `positiveRealAxisNet_not_eventually_constant`, `positiveRealAxisNet_index_not_small`, `positiveRealAxisNet_range_not_small` in [Surcomplex/TopologicalField.lean](../Surreal/Surcomplex/TopologicalField.lean) | The existing surcomplex field and fine topology form a Hausdorff topological division ring. Polynomial coordinate formulas give joint multiplication continuity; the nonzero norm-square denominator gives inverse continuity away from zero. Conjugation is a uniform equivalence, and the surreal real-axis inclusion is uniformly continuous. The positive-radius net on that axis is Cauchy and converges to zero but is never zero or eventually constant. Its index and range both fail lower-universe smallness. The original field, uniformity and topology are retained, with no square-root or real-closedness assumptions. **Proved** for these concrete assertions; build and axiom audit pass. |
| Order and algebraic-closedness obstructions in `found:sub:realclosed` | `Surreal.eval_X_sq_add_one_pos`, `not_isRoot_X_sq_add_one`, `orderedField_not_isAlgClosed`, `Foundations.SignSequence.not_isAlgClosed`, `Surcomplex.no_compatible_linearOrder` in [Surcomplex/OrderObstructions.lean](../Surreal/Surcomplex/OrderObstructions.lean) | Over every ordered field, the polynomial `X² + 1` is positive everywhere and has no root, excluding algebraic closedness. This applies to the actual sign field. Every proposed linear order on the existing surcomplex field fails ordered-ring compatibility because its imaginary unit squares to minus one. Neither argument assumes or proves real closedness of the sign field or algebraic closedness of the surcomplex field. **Proved**; build and axiom audit pass. |
| `found:eq:gram`, `found:eq:cauchyschwarz`, `trigonometry:eq:gram` | `Surreal.Complexify.gram_identity`, `cauchy_schwarz_sq`, `normSq_mul`, `mul_conj` | Generic algebraic identities and their ordered-field consequence. The scalar formula is proved independently of any surreal representation. **Prerequisites proved**; build and axiom audit pass. |
| `a:prop:triangle` | `Surreal.Complexify.modulus_mul`, `modulus_add_le`, `abs_re_le_modulus`, `abs_im_le_modulus`, `inv_eq_modulus` in [Modulus.lean](../Surreal/Algebra/Modulus.lean) | The stated identities over an ordered field with the proved nonnegative-square-root property, with modulus valued in that field. The concrete surcomplex interpretation is proved below. **Prerequisites proved**; build and axiom audit pass. |
| Nonnegative square-root obligation of `found:sub:realclosed` and `found:sub:modulus` | `Surreal.Foundations.SignSequence.squareRootTransition`, `squareRootTransition_sq_sub`, `IsSquareRootBracket`, `squareRootOptions`, `squareRootOptionCut`, `squareRootOptionCut_product_realized`, `squareRootOptionCut_sq_isPrefix`, `exists_nonneg_sq`, `existsUnique_nonneg_sq`, `sqrt`, `sqrt_sq`, `sqrt_sq_eq_abs` in [SignSequenceRoots.lean](../Surreal/Foundations/SignSequenceRoots.lean) | Every nonnegative element of the actual sign field has a unique nonnegative square root. Simplicity induction supplies roots of nonnegative canonical options. A countable closure under the rational transition `(x+a*b)/(a+b)` preserves square bracketing and lower-universe smallness; zero denominators are excluded and the all-zero product-option case is handled separately. Arbitrary-presentation multiplication proves one prefix direction for the candidate square, and the seed roots prove the reverse direction. A total square-root function is zero on negative inputs. This constructs roots without topological convergence, a Hahn bridge, or a real-closedness assumption. Odd-degree polynomial roots and real closedness remain pending. **Proved** for square roots; build and axiom audit pass. |
| Full `a:prop:triangle`; `found:sub:modulus`; concrete area/inequality clauses of `trigonometry:thm:heron` and `trigonometry:thm:ptolemy` | `Surreal.HasNonnegSquareRoots` in [OrderedSquareRoots.lean](../Surreal/Algebra/OrderedSquareRoots.lean); `SignSequence.signSequenceHasNonnegSquareRoots`, `Surcomplex.modulus`, `modulus_sq`, `modulus_mul`, `modulus_add_le`, coordinate bounds, `inv_eq_modulus`, `modulus_add_eq_iff_pos_quotient`, `heron`, `ptolemy`, `fineBall_eq_modulus`, `nhds_hasBasis_modulus`, `uniformity_hasBasis_modulus_sub`, `abs_sub_modulus_le`, `continuous_modulus` in [Surcomplex/Modulus.lean](../Surreal/Surcomplex/Modulus.lean) | The proved sign-field square roots instantiate the existing generic geometry through an explicit square-root property, automatically satisfied by real closed fields but strictly sufficient here without asserting real closedness. The actual surcomplex modulus is surreal-valued and satisfies every identity and inverse clause of the analysis proposition. Its positive-radius balls generate exactly the native fine topology and Cauchy uniformity; it obeys the reverse triangle estimate and is continuous. Heron, Ptolemy inequality, and the nonzero positive-quotient triangle-equality criterion apply to the concrete carrier. Angle/radius clauses, cyclic Ptolemy equality, and algebraic closedness remain pending. **Proved** for the full modulus proposition and these exact geometric/topological clauses; build and axiom audit pass. |
| Actual finite-ring, maximal-ideal, residue and decomposition clauses of `a:eq:st` | `Surreal.Surcomplex.IsFinite`, `IsInfinitesimal`, modulus-bound equivalences, `finiteSubring`, `finiteValuationSubring`, `standardPartHom`, `standardPartHom_surjective`, `standardPart_modulus`, `infinitesimalIdeal_isMaximal`, `standardPartQuotientEquiv`, `existsUnique_complex_infinitesimal_decomposition` in [Surcomplex/StandardPart.lean](../Surreal/Surcomplex/StandardPart.lean) | On the actual surcomplex field, coordinatewise standard part is a surjective ring homomorphism from the finite valuation subring to ordinary `ℂ`. Finiteness is exactly a natural modulus bound and infinitesimality exactly every positive reciprocal-natural bound. The kernel is the maximal infinitesimal ideal, its quotient is `ℂ`, and both terms of the ordinary-complex plus infinitesimal decomposition are unique. Standard part commutes with conjugation and sends the modulus of a finite element to the ordinary norm of its standard part. Identification with Hahn exponents and coefficient-zero extraction remains pending. **Proved** for these actual algebraic and modulus assertions; build and axiom audit pass. |
| Ordinary complex coefficient embedding for `a:eq:normal` and `a:eq:st` | `Surreal.Surcomplex.ofComplex`, `ofComplex_injective`, coordinate and conjugation compatibility, `normSq_ofComplex`, `modulus_ofComplex` in [ComplexEmbedding.lean](../Surreal/Surcomplex/ComplexEmbedding.lean) | Applies the actual ordered real embedding to both ordinary complex coordinates, giving an injective ring homomorphism into the constructed surcomplex field. Its actual modulus is the embedded ordinary complex norm. This supplies constants without identifying the ordinary and fine topologies or assuming algebraic closedness. **Proved**; build and axiom audit pass. |
| `found:cor:nopaths`, `a:cor:nopath` | `Surreal.Surcomplex.eq_of_isPreconnected_of_small_range`, `eq_of_isPreconnected`, `eq_of_continuous`, `eq_of_continuousOn_Icc` in [NoPaths.lean](../Surreal/Surcomplex/NoPaths.lean) | A fine-continuous map with permitted-small range is constant on every preconnected subset of its domain. Small index types suffice, including every ordinary real interval. This reuses Mathlib connectedness and the proved small-range discreteness of the actual fine topology, without requiring the whole surcomplex carrier to be small or discrete. **Proved**; build and axiom audit pass. |
| Arithmetic and modulus identities of `a:eq:valuation`; `a:lem:valbound` | `Surreal.Surcomplex.valuation`, `valuation_eq_modulus`, `valuation_mul`, `min_valuation_le_add`, `valuation_eq_min_coordinates`, `valuationSubring_eq_finiteValuationSubring`, finite/infinitesimal valuation characterizations, `tMonomial`, `valuation_surjective`, `isFinite_div_tMonomial_iff`, `isInfinitesimal_div_tMonomial_iff`, `modulus_lt_tMonomial_sub_one` in [Valuation.lean](../Surreal/Surcomplex/Valuation.lean) | Valuation of the actual modulus defines an additive surcomplex valuation with actual surreal values and infinity at zero. It equals the minimum of the coordinate valuations, restricts to the sign-field valuation, is invariant under conjugation, and has value zero on nonzero ordinary constants. Its valuation subring is exactly the existing finite ring. Scaling by `t^a` translates valuation bounds to finiteness or infinitesimality. Every bound `v(z) ≥ β` implies the source estimate `modulus(z) < t^(β-1)`, including zero. Infinite normal-form support identification remains separate. **Proved** for the actual valuation formulas and full bound lemma; build and axiom audit pass. |
| Actual leading-term decomposition and `a:eq:modulusleading` | `Surreal.Surcomplex.leadingExponent`, `normalized`, `leadingCoeff`, `finite_normalized`, `leadingCoeff_ne_zero`, `leadingCoeffMonoidWithZeroHom`, `exists_leading_error`, `valuation_lt_sub_leadingTerm`, `exists_modulus_leading_error`, `leadingCoeff_modulus` in [Leading.lean](../Surreal/Surcomplex/Leading.lean) | Dividing by the actual leading monomial gives a finite element with nonzero complex standard part for nonzero input. This constructs a leading coefficient, proves its multiplicative/inverse/division laws, and writes the element as its monomial times a constant plus an infinitesimal. Removing the leading term strictly raises valuation. The modulus has the same monomial and the ordinary norm of the complex leading coefficient, with an infinitesimal error. Zero is handled by explicit total conventions. **Proved** for these leading-term assertions and the modulus formula; identification with all coefficients of an infinite normal form remains pending. Build and axiom audit pass. |
| Full `a:prop:clopen`; fine continuity of standard part | `Surreal.Surcomplex.isClopen_setOf_isFinite`, `isClopen_setOf_isInfinitesimal`, `isClopen_monad`, `isClopen_affine_finite`, `isClopen_affine_infinitesimal`, `surcomplexTotallySeparatedSpace`, `finite_standardPart_fiber_eq_monad`, `isClopen_standardPart_fiber`, `isLocallyConstant_standardPartHom`, `continuous_standardPartHom` in [StandardPartTopology.lean](../Surreal/Surcomplex/StandardPartTopology.lean) | Both coordinate preimages are clopen, giving the actual finite ring and infinitesimal ideal as clopen subsets of the full fine topology. Every monad and nonzero affine image is clopen, with arbitrary centers including infinite elements. Coordinate separators give total separatedness and therefore total disconnectedness. On the genuine finite domain, ordinary-complex standard part is locally constant and continuous. The existing topology and uniformity are retained. **Proved** for the full proposition and these standard-part consequences; build and axiom audit pass. |
| `a:def:halo`, `a:rem:puncture`, `a:rem:halonotball` | `Surreal.Surcomplex.halo`, `halo_eq_iUnion_monads`, `mem_halo_iff_exists`, `affine_halo_eq`, `halo_punctured`, `halo_punctured_ne_remove_zero`, `isClopen_halo`, `isClopen_affine_halo`, `unitDiskBoundaryWitness`, `halo_unitDisk_ne_fineBall` in [Halos.lean](../Surreal/Surcomplex/Halos.lean) | A halo is exactly the finite-domain standard-part preimage, equivalently the union of the corresponding constant-plus-infinitesimal monads. Every halo and every nonzero affine chart is fine-clopen, even for arbitrary ordinary subsets. Deleting an ordinary point removes the whole monad; for domains containing zero this is proved different from deleting only zero, using a nonzero actual infinitesimal. The explicit point `1 - omega⁻¹` lies in the actual fine unit ball but has standard part one, so the halo of the ordinary unit disk is not that ball. **Proved** for these definitions and assertions; build and axiom audit pass. |
| `found:lem:nometric` and the following real-metric obstruction | `Surreal.Foundations.SignSequence.exists_positive_lower_bound_of_small`, `exists_positive_lower_bound_of_countable`; `Surcomplex.exists_ball_not_refined_by_small_family`, `exists_ball_not_refined_by_countable_family`, `not_isCountablyGenerated_nhds`, `not_has_countable_nhds_basis`, `not_firstCountableTopology`, `not_pseudoMetrizableSpace`, `not_metrizableSpace` in [NoMetric.lean](../Surreal/Surcomplex/NoMetric.lean) | A positive bound below every half-radius defeats every proposed small family of fine balls; arbitrary-universe countable index types are included through their smallness. No neighborhood filter at any actual surcomplex point is countably generated: a sequence in the punctured neighborhoods would contradict eventual equality for small-index convergent nets. This rules out arbitrary countable local bases, first countability and compatible real pseudometrics or metrics. The previously proved no-isolated-point result supplies the nondiscreteness clause. **Proved**; build and axiom audit pass. |
| `found:eq:rationalcircle`; affine clauses of `trigonometry:thm:cayley` | `Surreal.Complexify.normSq_circleParam`, `circleParam_ne_neg_one`, `circleCoord_circleParam`, `circleParam_circleCoord`, `circleParam_injective`, `circleEquiv` in [Circle.lean](../Surreal/Algebra/Circle.lean) | The rational affine chart and its inverse give an equivalence over any ordered field. The projective extension and direction multiplication are mapped below. The half-angle identity and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Projective and algebraic multiplication clauses of `trigonometry:thm:cayley`, `trigonometry:eq:cayley`, `trigonometry:eq:projectiveaddition` | `Surreal.Complexify.projectiveCircleEquiv`, `projectiveCircleEquiv_mk`, `circleParam_eq_fraction`, `projective_add_pair_ne_zero`, `projectiveAdd_mk`, `circleParam_mul`, `circleParam_mul_eq_neg_one_iff`, `projectiveAdd_infty_infty` in [ProjectiveCircle.lean](../Surreal/Algebra/ProjectiveCircle.lean) | Mathlib's actual projectivization of `Fin 2 → F` is equivalent to the norm-square-one circle over any ordered field. The chart has the homogeneous quotient formula and transports direction multiplication to `[ps+qr:qs-pr]`, whose output pair is proved nonzero. The affine rule applies exactly off its zero denominator; zero denominator gives `-1`, and two points at infinity give affine zero. Associativity and commutativity are also proved. The tangent/half-angle relation, infinitesimal proximity claim and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Factorization clauses of `polynomial:thm:fta`, `polynomial:eq:factorization`, `polynomial:eq:logderivative` | `Surreal.FinitePolynomial.exists_root`, `factorization`, `factorization_grouped`, `exists_unique_factorization`, `factorization_unique`, `sum_rootMultiplicities`, `logarithmic_derivative`, `logarithmic_derivative_grouped` in [Polynomial.lean](../Surreal/Algebra/Polynomial.lean) | Root existence, unique scalar/multiset factorization, grouped multiplicities and both logarithmic-derivative formulas. Existence assumes algebraic closedness; uniqueness holds over every field. The rational identities require a nonroot evaluation point. The fixed-Hahn closedness instance and explicit factorization specialization are now constructed below; transfer to the actual surcomplex field remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Division, gcd and ideal clauses of `polynomial:thm:fta`; gcd formula in `polynomial:eq:logderivative` | `Surreal.FinitePolynomial.exists_unique_division`, `exists_monic_gcd`, `gcd_bezout`, `ideal_principal`, `ideal_pair_eq_span_gcd`, `squarefree_iff_gcd_derivative_eq_one`, `gcd_derivative_rootMultiplicity`, `gcd_derivative_eq_prod` in [PolynomialDivision.lean](../Surreal/Algebra/PolynomialDivision.lean) | Unique division, normalized monic Bézout gcds and principal ideals over every field. The squarefree criterion assumes perfectness (supplied by characteristic zero); derivative multiplicities use characteristic zero. The grouped gcd product assumes a nonzero split polynomial and does not need monicity of the input. **Prerequisites proved**; build and axiom audit pass. |
| Multiplicity and Taylor clauses of `polynomial:thm:fta` | `Surreal.FinitePolynomial.multiplicity_eq_iff_derivatives`, `multiplicity_isLeast_nonzero_derivative`, `derivative_rootMultiplicity`, `multiple_root_iff`, `taylor_coeff_eq_derivative`, `taylor_eq_sum_derivatives`, `eq_sum_derivatives`, `eval_add_eq_sum_derivatives` in [PolynomialMultiplicity.lean](../Surreal/Algebra/PolynomialMultiplicity.lean) | The least nonvanishing derivative, derivative multiplicity and finite Taylor formulas over characteristic-zero fields. The least-index characterization explicitly excludes the zero polynomial. **Prerequisites proved**; build and axiom audit pass. |
| Binary clause of `polynomial:eq:factorlinear`; prerequisite of `polynomial:thm:hensel` | `Surreal.FinitePolynomial.factorLinearMap`, `factorLinearEquiv`, `factorCorrection`, `factorCorrection_spec`, `factorCorrection_unique`, `existsUnique_bounded_factor_correction`, `mul_perturbation_eq_linearization` in [PolynomialFactorLinearization.lean](../Surreal/Algebra/PolynomialFactorLinearization.lean) | Mathlib’s Sylvester map gives the linearization `(h,k) ↦ h*q+p*k` on perturbations below the factor degrees. A unit resultant makes it a linear equivalence for coprime factors with only the first required monic, over any commutative ring. The inverse provides unique bounded corrections with exact polynomial equality, and the quadratic remainder is explicit. Constant factors and the zero ring are included. The full finite-family version and support-controlled Hahn lifting are proved below; actual surreal transfer remains pending. **Proved** for the binary finite-algebra clause; build and axiom audit pass. |
| Full finite-family isomorphism `polynomial:eq:factorlinear` | `Surreal.FinitePolynomial.factorCofactor`, `factorLinearSum`, degree bounds, `factorLinearSum_injective_on_bounds`, `existsUnique_bounded_finite_factor_correction`, `finiteFactorLinearEquiv`, `finiteFactorCorrection`, exact forward/inverse formulas and uniqueness in [PolynomialFiniteFactorLinearization.lean](../Surreal/Algebra/PolynomialFiniteFactorLinearization.lean) | For any finite family of pairwise coprime monic polynomials, the cofactor-weighted sum is a linear equivalence from individually degree-bounded corrections to polynomials below the sum of factor degrees. Binary Sylvester inverses give the corrections modulo each factor; pairwise coprimality and monic degree bounds turn the resulting divisibility into exact equality. This holds over arbitrary commutative rings and includes empty families and degree-zero factors, hence specializes to the complete ordinary-complex assertion. Full support-controlled Hahn factorization is now mapped below; transfer to the actual sign field remains pending. **Proved** for the full finite-linearization equation; build and axiom audit pass. |
| Formal-parameter stage of `polynomial:thm:hensel` and `polynomial:eq:henselrecursion` | `Surreal.FinitePolynomial.factorLiftCoeff`, `factorLiftCoeff_eq`, `factorLift_linearization`, `liftedFactors_mul`, `liftedFactors_unique`, `existsUnique_formal_factorization` in [PowerSeriesFactorLifting.lean](../Surreal/Algebra/PowerSeriesFactorLifting.lean); `polynomialSeriesEmbedding`, `polynomialOfBoundedSeries`, `liftedPolynomials_mul`, `liftedPolynomials_isCoprime`, `existsUnique_monic_factorization_over_powerSeries` in [PowerSeriesPolynomialFactorLifting.lean](../Surreal/Algebra/PowerSeriesPolynomialFactorLifting.lean) | The bounded Sylvester inverse recursively constructs binary coprime factors in a natural-number formal parameter, with exact product and uniqueness among all bounded candidates. An injective variable interchange packages the factors as actual polynomials over `PowerSeries R`. Every monic polynomial of the prescribed degree whose constant specialization is a coprime monic product has unique monic lifts of the prescribed degrees and reductions. The constructed lifts remain coprime, using a unit resultant. Coefficient rings may have zero divisors; exact-degree existence states nontriviality explicitly. This proves the formal-parameter case, not arbitrary Hahn-support lifting or evaluation in the sign field. **Prerequisites proved**; build and axiom audit pass. |
| Multivariate formal stage of `polynomial:thm:hensel`, `polynomial:eq:henselrecursion` | `Surreal.FinitePolynomial.mvFactorLiftCoeff`, `mvFactorLift_linearization`, `existsUnique_mvFormal_factorization` in [MvPowerSeriesFactorLifting.lean](../Surreal/Algebra/MvPowerSeriesFactorLifting.lean); `polynomialMvSeriesEmbedding`, `polynomialOfBoundedMvSeries`, `existsUnique_monic_factorization_over_mvPowerSeries` in [MvPowerSeriesPolynomialFactorLifting.lean](../Surreal/Algebra/MvPowerSeriesPolynomialFactorLifting.lean); `universalMonicPerturbation` and its specialization formulas in [PolynomialUniversalPerturbation.lean](../Surreal/Algebra/PolynomialUniversalPerturbation.lean) | Recursion on total multiindex degree constructs unique bounded binary formal factors, with finite antidiagonals at every step. The parameter type may be arbitrary, including empty. Uniform polynomial-degree bounds give actual polynomials over the multivariate power-series ring. Any monic input with a coprime monic constant specialization has unique monic coprime factors of the prescribed degrees and reductions; nontriviality is explicit for exact-degree existence. A universal perturbation with one parameter for each lower coefficient specializes to every polynomial error below the leading degree. No Hahn evaluation is assumed in these formal statements. **Prerequisites proved**; build and axiom audit pass. |
| Full Hahn-field `polynomial:thm:hensel`, `polynomial:eq:henselfactor` | `Surreal.FinitePolynomial.BinaryMonicFactorLifting` and finite-family reduction theorems in [PolynomialFiniteFactorLifting.lean](../Surreal/Algebra/PolynomialFiniteFactorLifting.lean); `Surreal.HahnSeries.exists_monic_factorization_with_support_of_standardPart`, `existsUnique_monic_factorization_of_standardPart`, `existsUnique_monic_finite_factorization_of_standardPart`, ambient coefficient/error forms in [PolynomialFactorLifting.lean](../Surreal/HahnSeries/PolynomialFactorLifting.lean); `support_finite_factor_coeff_subset_residueErrorSupport`, `degree_factor_correction_lt`, `support_finite_factor_correction_subset`, `existsUnique_monic_finite_factorization_with_support` in [PolynomialFiniteFactorSupport.lean](../Surreal/HahnSeries/PolynomialFiniteFactorSupport.lean) | Every finite coprime monic residue factorization of a monic polynomial over the nonnegative-order Hahn ring lifts uniquely to monic factors of the same degrees. Universal formal factors are evaluated at the actual finitely many coefficient errors, supplying existence without an assumed lift or summation map. Every correction has lower polynomial degree, positive-order coefficients and support inside the original error monoid with zero removed. Binary comparison against the original polynomial gives the common support bound for every factor; uniqueness also holds among candidates without that bound. Coprimeness already holds over the valuation ring, hence over the ambient field. Empty families, constant factors and arbitrary characteristic are allowed; no divisibility or rank restriction on the exponent group is used. **Proved** for the full theorem in its explicitly fixed Hahn workspace. Transfer to the actual surcomplex carrier remains a separate bridge. Build and axiom audit pass. |
| Full Hahn-field `polynomial:cor:simpleroot`, `polynomial:eq:firstrootcorrection` | `Surreal.HahnSeries.exists_supported_root_of_simple_standardPart`, `existsUnique_infinitesimal_root_correction`, `existsUnique_supported_root_correction` in [PolynomialSimpleRootLifting.lean](../Surreal/HahnSeries/PolynomialSimpleRootLifting.lean); `coeff_eval_constant`, `first_root_correction_linear_identity`, `first_root_correction_coeff` in [PolynomialFirstRootCorrection.lean](../Surreal/HahnSeries/PolynomialFirstRootCorrection.lean); `orderTop_supported_correction_ge`, `exists_least_coefficient_support`, `existsUnique_supported_root_correction_with_coefficients`, `existsUnique_supported_root_correction_at_least_error_exponent` in [PolynomialSimpleRootCorrection.lean](../Surreal/HahnSeries/PolynomialSimpleRootCorrection.lean) | Every simple residue root lifts uniquely with positive correction support in the original error monoid minus zero. A common nonnegative lower bound for the input supports bounds each nonzero element of their additive closure. At any positive common lower bound, Taylor expansion eliminates the quadratic terms and gives the stated first-coefficient formula, including cancellation. The least input exponent exists for every nonzero error polynomial; zero error needs no artificial minimum. Evaluation of the coefficient polynomial identifies the numerator with the source's `E_e(c)`. Uniqueness compares all positive-order root corrections. No algebraic closedness, divisibility or Archimedean hypothesis is used. **Proved** for the full fixed-Hahn corollary; actual surreal transfer remains pending. Build and axiom audit pass. |
| Full Hahn-field `polynomial:cor:clusterfactor` | `Surreal.HahnSeries.isRoot_cluster_factor_iff`, `isRoot_map_cluster_factor_iff`, `existsUnique_cluster_factors`, `residueRootSet`, `residueMultiplicity`, `existsUnique_canonical_cluster_factors_of_splits`, `existsUnique_complex_cluster_factors` in [PolynomialClusterFactors.lean](../Surreal/HahnSeries/PolynomialClusterFactors.lean) | The actual distinct residue roots index unique monic cluster factors of their ordinary multiplicity degrees, with exact product, pairwise coprimeness and correction support in the original error monoid minus zero. A factor's ambient Hahn roots are exactly the original roots with its prescribed standard part: the existing monic-root valuation bound proves those roots finite before reduction. Splitting is required only for the ordinary residue polynomial and supplied automatically by Mathlib for complex coefficients. No Hahn algebraic-closedness or divisible-exponent assumption is used, and no individual splitting of multiple clusters is asserted. Empty root sets and constant monic inputs are included. **Proved** for the full fixed-Hahn corollary; actual surreal transfer remains pending. Build and axiom audit pass. |
| Local kernel calculation for `polynomial:thm:crt` | `Surreal.FinitePolynomial.pow_linear_dvd_iff_derivatives_vanish`, `derivative_jets_eq_iff_dvd_sub` | A jet vanishes exactly when the corresponding power of `X - a` divides the polynomial; equal jets correspond to divisibility of the difference. These include zero polynomials. **Prerequisites proved**; build and axiom audit pass. |
| Hermite interpolation clause of `polynomial:thm:crt` | `Surreal.FinitePolynomial.exists_unique_interpolation_representative`, `exists_unique_hermite_interpolant`, `exists_unique_hermite_interpolant_fin` in [PolynomialInterpolation.lean](../Surreal/Algebra/PolynomialInterpolation.lean) | Arbitrary finite derivative jets at distinct nodes determine a unique polynomial of degree below the sum of multiplicities, over a characteristic-zero field. Zero multiplicities and the empty index type are included. Other finite CRT clauses are mapped separately below. **Prerequisites proved**; build and axiom audit pass. |
| Quotient and idempotent clauses of `polynomial:thm:crt`, `polynomial:eq:finiteCRT` | `Surreal.FinitePolynomial.polynomialCRT`, `polynomialCRT_mk_derivative_jet`, `crtIdempotent`, `mk_eq_crtIdempotent_of_local_congruences`, `exists_crtIdempotent_representative`, `crtIdempotent_mul_self`, `crtIdempotent_mul_of_ne`, `sum_crtIdempotent` in [PolynomialCRT.lean](../Surreal/Algebra/PolynomialCRT.lean) | The quotient by the product of local moduli is ring-isomorphic to the product of truncated polynomial rings. Its Taylor forward map has the displayed derivative-jet formula in characteristic zero. Coordinate idempotents are orthogonal and sum to one, with bounded-degree representatives and a local-congruence criterion. Empty indices and zero multiplicities are included. Concrete representatives and the simple-root formula are mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Explicit local inverse and `PᵢCᵢ` representatives in `polynomial:thm:crt` | `Surreal.FinitePolynomial.inverseJet`, `inverseJet_eq_sum`, `node_pow_dvd_mul_inverseJet_sub_one`, `inverseJet_unique`, `interpolationCofactor_eq_div`, `interpolationCofactor_eval_ne_zero`, `inverseJetIdempotentPolynomial_degree_lt`, `mk_inverseJetIdempotentPolynomial` in [PolynomialInverseJet.lean](../Surreal/Algebra/PolynomialInverseJet.lean) | Truncating the actual reciprocal formal Taylor series gives the unique local inverse of degree below the multiplicity. The cofactor is exactly `P / Aᵢ` and is nonzero at its node. Each product `PᵢCᵢ` has degree below the total multiplicity, satisfies all local congruences, and represents the coordinate idempotent. Works over every field, including zero multiplicities. The derivative formula is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Constructive interpolant in the proof of `polynomial:thm:crt` | `Surreal.FinitePolynomial.hermiteInterpolant`, `hermiteInterpolant_local_congruences`, `hermiteInterpolant_degree_lt`, `hermiteInterpolant_unique`, `polynomialCRT_hermiteInterpolant`, `polynomialCRT_symm_mk`, `hermiteJetInterpolant_derivative`, `hermiteJetInterpolant_unique` in [PolynomialHermiteFormula.lean](../Surreal/Algebra/PolynomialHermiteFormula.lean) | The remainder modulo `P` of the explicit finite sum `∑ᵢ PᵢCᵢqᵢ` is the unique interpolant below the total-multiplicity degree bound with the prescribed polynomial residue classes. Its image under the CRT equivalence is the translated tuple, and translating local-variable representatives back gives the explicit inverse of that equivalence. Choosing the local Taylor representatives realizes the requested derivative jets in characteristic zero. Empty node sets and zero multiplicities are included. **Prerequisites proved**; build and axiom audit pass. |
| Formal reciprocal derivative formula in `polynomial:eq:inversejet` | `Surreal.FinitePolynomial.constantCoeff_iterate_powerSeries_derivative`, `reciprocalDerivativeNumerator`, `iterate_derivative_inverse_taylor`, `inverseJet_eq_sum_formal_derivatives`, `inverseJet_eq_sum_reciprocal_numerators`, `reciprocal_jet_denominator_ne_zero` in [PolynomialRationalJets.lean](../Surreal/Algebra/PolynomialRationalJets.lean) | In characteristic zero, the inverse jet coefficients are the iterated derivatives of the reciprocal Taylor series at zero divided by factorials. The repeated quotient-rule numerator recurrence is verified using Mathlib's actual formal derivative, yielding explicit coefficients `Nⱼ(a)/(q(a)^(j+1)·j!)` with nonzero denominators when `q(a) ≠ 0`. This is an algebraic local formal-series interpretation; a global `RatFunc` derivative operator and comparison with analytic derivatives are not supplied. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:lambdadef`; finite quotient prerequisites of `polynomial:thm:trace` | `Surreal.FinitePolynomial.residueFunctional`, `residueFunctional_mk`, `quotient_powerBasis_repr`, `quotient_leftMulMatrix`, `quotient_trace_eq_sum`, `quotient_norm_eq_det`, `map_monic_remainder_coeff` in [PolynomialQuotient.lean](../Surreal/Algebra/PolynomialQuotient.lean) | Uses Mathlib's `AdjoinRoot`, monic remainder and power basis over any commutative ring. Multiplication-matrix entries and trace are explicit remainder coefficients; the norm is their determinant. Coefficient maps commute with monic remainder extraction, without inverse coefficients. The universal norm/resultant identity is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Perfection and explicit dual-basis clauses of `polynomial:thm:residuepairing`, `polynomial:eq:dualbasis`, `polynomial:eq:eulerderivative` | `Surreal.FinitePolynomial.dualPolynomial`, `coeff_dualPolynomial`, `sum_X_pow_mul_dualPolynomial`, `coeff_modByMonic_X_pow_mul_dualPolynomial`, `residueFunctional_root_pow_mul_dualPolynomial` in [PolynomialResidueDual.lean](../Surreal/Algebra/PolynomialResidueDual.lean); `residuePairingEquiv`, `residuePairingEquiv_symm_apply`, `residueDualBasis`, `residueDualBasis_apply`, `quotient_repr_eq_residue` in [PolynomialResiduePairing.lean](../Surreal/Algebra/PolynomialResiduePairing.lean) | The displayed finite dual polynomials satisfy the Kronecker pairing identity and the Euler derivative sum. The pairing is a linear equivalence from the quotient to its linear dual, with an explicit finite-sum inverse; the dual vectors form an actual basis. All statements hold over arbitrary commutative rings, including zero divisors and the zero ring, with no separability or characteristic hypothesis. Degree zero is included by empty index types. Gram determinant and the inverse coefficient matrix are mapped separately below. The Gram, bivariate Bézout-kernel and Laurent-coefficient identities are mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Universal trace identity in `polynomial:thm:trace`, `polynomial:eq:traceidentity` | `Surreal.FinitePolynomial.quotient_sum_basis_mul_dual`, `quotient_trace_eq_residue_derivative`, `quotient_trace_mk_eq_coeff` in [PolynomialResiduePairing.lean](../Surreal/Algebra/PolynomialResiduePairing.lean) | Multiplication trace is exactly `λ(P′h)` over any commutative ring. For a polynomial representative it is the top coefficient of `(P′Q) %ₘ P`, with the derivative and trace both taken from Mathlib. The proof uses the explicit dual basis and finite Euler sum, so remains valid at collisions and in positive characteristic. The trace Gram factorization, universal discriminant equality and norm/resultant identities are mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Gram determinant and inverse coefficient matrix in `polynomial:thm:residuepairing`, `polynomial:eq:gramdet` | `Surreal.FinitePolynomial.residueGram`, `residueGram_entry_eq_zero`, `residueGram_entry_eq_one`, `det_residueGram`, `dualCoefficientMatrix`, `residueGram_mul_dualCoefficientMatrix`, `residueGram_inv_eq_dualCoefficientMatrix` in [PolynomialResidueGram.lean](../Surreal/Algebra/PolynomialResidueGram.lean) | Reversing columns gives a lower triangular matrix with diagonal one, so its determinant is exactly `(-1)^(n(n-1)/2)`. The matrix with entries `P.coeff(i+j+1)` is proved to be the inverse Gram matrix through the explicit residue-dual basis. These statements hold over any commutative ring, at repeated roots and in degree zero. The bivariate divided-difference identity is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Bézout-kernel clause of `polynomial:thm:residuepairing`, `polynomial:eq:bezoutkernel` | `Surreal.FinitePolynomial.bezoutKernel`, `coeff_bezoutKernel`, `coeff_coeff_bezoutKernel`, `sub_mul_bezoutKernel`, `bezoutKernel_coefficientMatrix`, `residueGram_inv_eq_bezoutKernel_coefficientMatrix` in [PolynomialBezoutKernel.lean](../Surreal/Algebra/PolynomialBezoutKernel.lean) | The finite bivariate polynomial has exactly the explicit dual polynomials as coefficient columns and satisfies `(z-Y)Δ = P(z)-P(Y)` over every commutative ring. This realizes the polynomial difference quotient without dividing by a nonunit. Its finite coefficient matrix is the inverse residue Gram matrix for monic `P`. The polynomial identity itself needs no monicity, and degree-zero/zero-ring cases are included. The separate Laurent-coefficient identity at infinity is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Matrix factorization clause of `polynomial:eq:tracegram` | `Surreal.FinitePolynomial.residueGram_eq_pairing`, `quotient_traceMatrix_eq_residueGram_mul`, `quotient_det_traceMatrix_eq_sign_mul_norm` in [PolynomialTraceGram.lean](../Surreal/Algebra/PolynomialTraceGram.lean) | Mathlib's native trace matrix in the quotient power basis equals the residue Gram matrix times the multiplication matrix of the derivative. Its determinant is the fixed residue sign times the native quotient norm of the derivative. All coefficient rings are commutative; no separability or nonvanishing determinant assumption is needed. The universal identification with the native polynomial discriminant is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Determinant/resultant and discriminant clauses of `polynomial:thm:trace`, `polynomial:eq:tracegram` | `Surreal.FinitePolynomial.quotient_norm_eq_resultant`, `monic_resultant_derivative_eq_sign_mul_discr`, `quotient_det_traceMatrix_eq_discr` in [PolynomialNormResultant.lean](../Surreal/Algebra/PolynomialNormResultant.lean) | The determinant of multiplication by `Q` on the actual monic quotient is the native resultant `Res(P,Q)` over every commutative ring. Together with residue duality this identifies the native trace Gram determinant with the native polynomial discriminant. Mathlib's universal-coefficient induction descends degree-preserving remainder matrices from a splitting field; it does not assume the quotient is reduced or separable. Monicity removes derivative-degree padding, including degree drops in positive characteristic. Degree-zero and zero-ring cases are included. Combined with the trace and Gram rows above, this proves every assertion of the universal-ring trace theorem. **Proved**; build and axiom audit pass. |
| `polynomial:eq:lambdaatinfinity` in the residue-duality proof | `Surreal.FinitePolynomial.polynomialAtInfinity`, `reciprocalAtInfinity`, `polynomialAtInfinity_mul_reciprocal`, `quotientAtInfinity`, `polynomialAtInfinity_mul_quotient`, `quotientAtInfinity_eq_remainder_add_polynomial`, `coeff_quotientAtInfinity_eq_remainder`, `residueFunctional_eq_coeff_quotientAtInfinity` in [PolynomialResidueInfinity.lean](../Surreal/Algebra/PolynomialResidueInfinity.lean) | In Mathlib's actual Laurent series over any commutative ring, the variable is `T=z⁻¹`. Monicity supplies a unit-constant reciprocal of the reversed polynomial, and multiplication verifies the Laurent inverse and quotient. The coefficient of `T¹` in `Q/P` is exactly the top monic remainder coefficient. Polynomial parts have no positive Laurent exponents; degree-zero monic inputs and the zero ring are included. No field, ordinary analytic convergence or root-separation denominator is required. **Proved**; build and axiom audit pass. |
| Simple-root clause of `polynomial:thm:crt`, `polynomial:eq:lagrange` | `Surreal.FinitePolynomial.lagrange_formula`, `nodal_derivative_eval`, `nodal_derivative_eval_ne_zero`, `eval_lagrange_formula`, `lagrange_denominator_ne_zero` in [PolynomialLagrange.lean](../Surreal/Algebra/PolynomialLagrange.lean) | The displayed Lagrange polynomial identity reuses Mathlib's nodal polynomial and exact division by its selected linear factor. The scalar rational formula is proved away from the nodes, with every denominator nonzero. Valid over any field, without a lower bound on node separation; the degree hypothesis also handles an empty node set. Surcomplex specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Viète coefficient identity preceding `polynomial:eq:newton1`; `polynomial:eq:newton1`, `polynomial:eq:newton2` | `Surreal.FinitePolynomial.rootPowerSum`, `vieta_prod_coefficient`, `vieta_coefficient`, `newton_multiset_uniform`, `newton_identity_le_degree`, `newton_identity_gt_degree` in [PolynomialNewton.lean](../Surreal/Algebra/PolynomialNewton.lean) | The coefficient and both Newton identities are proved for monic split polynomials with roots counted as a multiset. The first regime requires `0 < k ≤ n`; the second includes degree-zero polynomials. Generic finite multiset identities hold over every commutative ring, and the field specializations impose no characteristic-zero assumption. Uses Mathlib's universal symmetric-polynomial identities with finite evaluation. Surcomplex specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:resultantproduct` and surrounding determinant, specialization, interchange-sign and common-root assertions | `Surreal.FinitePolynomial.resultant_eq_leadingCoeff_mul_prod_eval`, `resultant_eq_leadingCoeffs_mul_prod_sub`, `resultant_swap`, `resultant_eq_sylvester_det`, `sylvester_eq_matrix_bezout`, `resultant_map_fixed_degrees`, `resultant_map_of_injective`, `resultant_eq_zero_iff_common_root`, `sylvester_has_kernel_iff_common_root`, `resultant_ne_zero_iff_isCoprime` in [PolynomialResultant.lean](../Surreal/Algebra/PolynomialResultant.lean) | Mathlib's resultant at the actual degrees has the root products with both leading-coefficient powers and the Sylvester determinant interpretation. Arbitrary coefficient maps preserve a fixed-size determinant; injectivity additionally preserves actual degrees. The common-root criterion assumes the first polynomial is nonzero and split, and permits a zero second polynomial. The finite Bézout map is identified with the Sylvester matrix in explicit bases, and a nonzero kernel vector characterizes common roots. Coprimality requires no splitting. Native `Res(0,0)=1` is documented. Discriminants and Hahn valuation identities are mapped separately below. Quotient multiplication determinants are mapped separately with the universal trace theorem; surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:discdef` and its repeated-root assertion | `Surreal.FinitePolynomial.leadingCoeff_mul_discr_eq_sign_mul_resultant`, `discr_eq_sign_mul_resultant`, `discr_ne_zero_iff_squarefree`, `discr_eq_zero_iff_repeated_root`, `discr_C_mul_prod_X_sub_C`, `discr_prod_X_sub_C`, `discr_eq_leadingCoeff_pow_mul_prod_sub_sq` in [PolynomialDiscriminant.lean](../Surreal/Algebra/PolynomialDiscriminant.lean) | Uses Mathlib's native discriminant and actual-degree resultant in characteristic zero. The squared root-difference formula includes the leading-coefficient power and counts repeated root occurrences. Positive degree guards the general formula; monic constants and native discriminant-one conventions are included. The squarefree criterion needs no splitting, while the repeated-root criterion assumes a nonzero split polynomial. Valuation and quotient trace-pairing identities are mapped separately; surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:prop:rootbounds`, `polynomial:eq:cauchybound` | `Surreal.FinitePolynomial.root_lt_cauchy_bound`, `reciprocal_cauchy_bound_lt_root`, `root_le_two_mul_radialCoefficientMax`, `root_eq_zero_of_radialCoefficientMax_eq_zero`; `Surreal.Complexify.modulus_root_lt_cauchy_bound`, `reciprocal_cauchy_bound_lt_modulus_root`, `modulus_root_le_two_mul_radialCoefficientMax` in [PolynomialRootBounds.lean](../Surreal/Algebra/PolynomialRootBounds.lean) | Both strict Cauchy bounds use the exact finite maxima in the source, with a nonzero constant coefficient for the lower bound. The radial maximum uses nonnegative `(n-j)`th roots in a real closed ordered base field and proves the non-strict bound `2M`, including the zero-maximum conclusion. The abstract proofs use an ordered-field-valued absolute value, specialized to the existing base-field modulus of `Complexify F`; no Archimedean assumption or real-valued norm is introduced. Positive degree makes all maxima nonempty. The strict Cauchy bounds and certified-radius bound are instantiated on concrete surcomplex numbers below; the exact arbitrary-root radial maximum remains pending there. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:thm:gausslucas`, `polynomial:eq:barycentric` | `Surreal.FinitePolynomial.critical_point_eq_barycentric_grouped`, `groupedCriticalRootWeight_pos`, `normalizedCriticalRootWeight_pos`, `sum_normalizedCriticalRootWeight`, `sum_normalizedCriticalRootWeight_smul`, `critical_point_mem_convexHull_roots`, `iterate_derivative_roots_subset_convexHull` in [PolynomialGaussLucas.lean](../Surreal/Algebra/PolynomialGaussLucas.lean) | The exact barycentric identity is proved both by root occurrences and with grouped algebraic multiplicities. Nonroot critical points have strictly positive base-field-valued weights with sum one. The native convex hull uses the ordered field `F` with nonnegative square roots, including non-Archimedean fields, and also contains critical points which are roots. The first-derivative theorem assumes splitting and positive degree; higher derivatives assume splitting of each preceding derivative and nonvanishing of the final derivative. The concrete surcomplex specialization under these same splitting hypotheses is proved below; unconditional splitting and algebraic closedness remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Concrete Cauchy clauses of `polynomial:prop:rootbounds` / `polynomial:eq:cauchybound`; split-case `polynomial:thm:gausslucas` and `polynomial:eq:barycentric` | `Surreal.Surcomplex.modulusAbsoluteValue`, `root_lt_cauchy_bound`, `reciprocal_cauchy_bound_lt_root`, `root_le_two_mul_of_coeff_le_pow`, `critical_point_eq_barycentric_grouped`, `critical_point_mem_convexHull_roots`, `iterate_derivative_roots_subset_convexHull` in [Surcomplex/PolynomialGeometry.lean](../Surreal/Surcomplex/PolynomialGeometry.lean) | Both strict source Cauchy bounds hold for roots of actual surcomplex polynomials with positive degree, retaining the nonzero constant-coefficient guard for the lower bound. An explicit coefficient-domination certificate gives the radial bound without requiring arbitrary-degree roots. Gauss–Lucas and the exact grouped barycentric formula hold on the concrete carrier under explicit splitting; nonroot critical points are required for the displayed weights. Higher derivatives retain splitting of every preceding derivative and nonvanishing of the final one. The modulus and convex coefficients are surreal-valued. **Proved** for the Cauchy and certified-radius clauses; **prerequisites proved** for the full Gauss–Lucas statement. Algebraic closedness/unconditional splitting and the source radial maximum involving arbitrary-degree roots remain pending. Build and axiom audit pass. |
| `polynomial:eq:resval` and the nodal derivative separation sum defining `dᵢ` | `Surreal.HahnSeries.orderTop_resultant_eq_sum_eval`, `orderTop_resultant`, `order_resultant`, `orderTop_nodal_derivative_eval`, `order_nodal_derivative_eval` in [PolynomialValuation.lean](../Surreal/HahnSeries/PolynomialValuation.lean) | Resultant valuations retain the leading-coefficient powers and every root-pair occurrence. The formulas with `orderTop` retain infinity when products vanish; exponent-group-valued `order` formulas require nonzero polynomials/resultant or injective nodes. Splitting is explicit, and no Hahn algebraic closedness or surreal embedding is assumed. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:discval` | `Surreal.HahnSeries.orderTop_discr_eq_pair_sum`, `order_discr_eq_pair_sum`, `orderTop_discr_eq_sum_derivative`, `order_discr_eq_sum_derivative` in [DiscriminantValuation.lean](../Surreal/HahnSeries/DiscriminantValuation.lean) | Over a characteristic-zero Hahn coefficient field, the discriminant valuation is the leading-coefficient term plus twice the pairwise separation sum. The positive-degree formula uses an explicit indexed factorization; injective roots give the exponent-group-valued version. For monic split polynomials, it is also the sum of derivative valuations at root occurrences, including the degree-zero empty sum. The `orderTop` versions permit vanishing discriminants; the finite monic version requires a nonzero discriminant. Hahn algebraic closedness and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:weighted`, `polynomial:eq:active`, `polynomial:lem:gaussvaluation` and following normalization assertions | `Surreal.HahnSeries.gaussExpansion`, `coeff_coeff_gaussExpansion`, `gaussExpansion_injective`, `weightedGaussVal`, `weightedGaussVal_eq_inf`, `weightedGaussVal_mul`, `weightedGaussVal_add`, `gaussInitial_ne_zero`, `gaussInitial_mul`, `orderTop_normalizedGaussCoefficient_nonneg`, `coeff_gaussInitial_eq_standardPart`, `exists_normalizedGaussCoefficient_orderTop_eq_zero`, `coeff_gaussInitial_ne_zero_iff`, `support_gaussInitial_eq_active`, `gaussInitial_active_extrema` in [PolynomialGaussValuation.lean](../Surreal/HahnSeries/PolynomialGaussValuation.lean) | Regrouping a finite polynomial into Hahn series with polynomial coefficients defines a faithful expansion at any center and any weight in the ordered exponent group. Its native Hahn valuation is exactly the finite minimum of weighted Taylor-coefficient valuations; infinity occurs precisely at the zero polynomial. Leading coefficients give nonzero multiplicative initial polynomials, and the coefficient-zero residue map extracts their normalized coefficients. Every normalized coefficient has nonnegative order and at least one has order zero for nonzero input. No Archimedean, divisibility, characteristic-zero or algebraic-closedness assumption is imposed. The initial support consists exactly of the active indices, and its trailing degree and degree are their least and greatest elements. Root counts for explicitly split polynomials are mapped below; the surreal bridge remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:thm:initialroots`, `polynomial:eq:initialroots`, `polynomial:eq:profileproduct`, `polynomial:eq:closedcount`, `polynomial:eq:opencount`, `polynomial:eq:shellcount` | `Surreal.HahnSeries.weightedGaussVal_X_sub_C`, `weightedGaussVal_split`, `gaussInitial_split_standardPart`, `initialRootScalar_ne_zero`, `natDegree_gaussInitial_split`, `natTrailingDegree_gaussInitial_split`, `shell_count_gaussInitial_split`, `rootMultiplicity_gaussInitial_split_direction` in [PolynomialInitialRoots.lean](../Surreal/HahnSeries/PolynomialInitialRoots.lean) | For an explicit finite factorization, the weighted profile is the leading-scalar valuation plus the sum of root-separation minima. The initial polynomial has the exact standard-part factors for closed-ball roots and an explicit nonzero scalar from outside roots. Its degree, trailing degree and their difference count closed/open/shell roots with multiplicities; the multiplicity of each residue counts the corresponding residue-direction ball. Repeated roots, coincident residues, empty products and roots at the center with valuation infinity are retained. Counting assumes a nonzero leading scalar. Combined with active-index extrema above this gives the source's `j₋` and `j₊` counts. No algebraic closedness, characteristic-zero, divisible-group or rank-one assumption is introduced. The concrete surreal bridge remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:cor:valrouche`, `polynomial:eq:valrouche` | `Surreal.HahnSeries.weightedGaussVal_add_eq_of_lt`, `gaussInitial_add_eq_of_lt`, `valuationRouche`, `valuationRouche_closed_count`, `valuationRouche_open_count`, `valuationRouche_shell_count`, `valuationRouche_direction_count` in [PolynomialRouche.lean](../Surreal/HahnSeries/PolynomialRouche.lean) | A perturbation of strictly higher weighted valuation preserves the exact profile value and entire initial polynomial, including its scalar. Zero error is included by valuation infinity; the strict hypothesis already forces the original polynomial to be nonzero. Root-count consequences use independent nonzero finite split factorizations of the two polynomials, allowing different degrees and root index types while preserving multiplicities. No contour, topology, algebraic-closedness, characteristic or rank assumption is introduced. Concrete surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:thm:newton`, actual breakpoint finiteness and leading-coefficient multiplicities | `Surreal.HahnSeries.newtonActiveIndices`, `newtonSpan`, `rootValuationCount_eq_newtonSpan`, `rootValuationCount_eq_of_active_extrema`, `newtonBreakpoint_iff_exists_root`, `isRoot_newtonBreakpoint_order`, `infinite_valuation_root_count`, `rootMultiplicity_initial_eq_leadingCoeff_count`, `mem_newtonBreakpointValues`, `finite_newtonBreakpoints` in [PolynomialNewtonProfile.lean](../Surreal/HahnSeries/PolynomialNewtonProfile.lean) | At center zero, the largest minus smallest active index counts the multiset of roots at the chosen `Γ`-valued threshold, excluding `⊤`. At least two active indices occur exactly at the valuations of nonzero roots. Nonzero initial-root multiplicities count original roots with that valuation and leading coefficient; zero roots are counted separately at infinity. The finite set of nonzero-root orders is exactly the breakpoint set. The polynomial is nonzero and explicitly split; arbitrary ordered exponent groups are allowed. Constructing candidate breakpoints by rational coefficient slopes, affine-region slope analysis and the surreal interpretation remain separate obligations. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:lem:initialderivative`, `polynomial:eq:initialderivative` | `Surreal.HahnSeries.gaussExpansion_derivative`, `centeredGaussExpansion_derivative`, `normalizedGaussExpansion_derivative`, `weightedGaussVal_derivative`, `gaussInitial_derivative`, `initialDerivative`, `initialIterateDerivative` in [PolynomialInitialDerivative.lean](../Surreal/HahnSeries/PolynomialInitialDerivative.lean) | The exact formal chain rule shifts Hahn exponents by the scale. If the leading initial polynomial has nonzero derivative, differentiation lowers the weighted value by the scale and gives exactly its ordinary derivative as the new initial polynomial. In residue characteristic zero, positive initial degree suffices; all iterates through that degree have value `w(P)-rρ` and initial polynomial `I(P)^(r)`. The zeroth iterate is included and finite shifts use `WithTop` without assigning a finite order to zero. No constant-initial or positive-characteristic nonvanishing claim is assumed. Concrete surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:thm:criticalballs`; all-root-ball containment clause of `polynomial:cor:nearest` | `Surreal.HahnSeries.closedBallRootCount`, `openBallRootCount`, `closedBallRootCount_iterate_derivative`, `openBallRootCount_iterate_derivative`, `directionRootCount_iterate_derivative`, `critical_direction_count`, `criticalPoint_mem_closedBall`, `criticalPoint_mem_openBall` in [PolynomialCriticalBalls.lean](../Surreal/HahnSeries/PolynomialCriticalBalls.lean) | Native root multisets count multiplicities in closed/open valuation balls. If the original count is `k`, the `r`th derivative has count `k-r` for `r≤k`, with occupation forced whenever `r>0`; the zeroth case is included. The relevant derivative is proved nonzero even at `r=k`. Its residue-direction multiplicities are those of the corresponding initial derivative. Every closed or open ball containing all roots also contains all critical points. Residue characteristic zero and splitting of the original and relevant derivative are explicit. The nearest-neighbour maximum equality is proved below; Hahn algebraic closedness and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Nearest-neighbour clause of `polynomial:cor:nearest`; `polynomial:eq:nearest` | `Surreal.HahnSeries.criticalPoint_orderTop_le_of_otherRoots_le`, `exists_criticalPoint_orderTop_eq_of_nearest_root`, `otherRootValues`, `criticalPointValues`, `nearestCriticalValue` in [PolynomialNearestCritical.lean](../Surreal/HahnSeries/PolynomialNearestCritical.lean) | For a squarefree polynomial of degree at least two, the finite valuations of displacements from a chosen root to other roots and to critical points have a common attained greatest element. No critical point equals the chosen root. Open-ball count one excludes every closer critical point; closed-ball count at least two supplies a critical point on the nearest-root shell. Both the polynomial and its derivative explicitly split, and residue characteristic zero is retained. Valuations of zero are excluded before finite-order comparisons. Hahn algebraic closedness and concrete surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `trigonometry:eq:dotcross`, `trigonometry:eq:gram` and following triangle-equality characterization | `Surreal.Complexify.dot`, `cross`, `dot_sq_add_cross_sq`, `abs_dot_le`, `modulus_add_eq_iff_dot`, `modulus_add_eq_iff_pos_quotient` in [Geometry.lean](../Surreal/Algebra/Geometry.lean) | Coordinate identities and the equality criterion for nonzero vectors over any ordered field with nonnegative square roots. The positive quotient is an embedded element of that same base field. The concrete surcomplex equality criterion is proved below. **Prerequisites proved**; build and axiom audit pass. |
| Area clause of `trigonometry:thm:heron`, factorization behind `trigonometry:eq:heronfactor` | `Surreal.Complexify.heron_factorization`, `heron`, `triangleArea` | Heron's identity for the triangle with vertices `0,z,w`, including degenerate cases, over an ordered field with nonnegative square roots. The concrete surcomplex specialization is proved below; radius, incenter, bisector and half-angle clauses remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Inequality clause of `trigonometry:thm:ptolemy` | `Surreal.Complexify.ptolemy_identity`, `ptolemy` | The four-point inequality over any real closed ordered base field. Cyclic order and the cyclic equality case remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Finite normalization for the Hahn closedness assertions in `found:sub:hahncomplex`, `polynomial:prop:workspace` | `Surreal.FinitePolynomial.scalePolynomial`, degree, coefficient, reconstruction and affine root-pullback formulas in [PolynomialScaling.lean](../Surreal/Algebra/PolynomialScaling.lean); `exists_coprime_monic_factors`, `exists_odd_coprime_monic_factors_of_root`, `realClosed_depressed_odd_coprime_factorization` in [RealClosedPolynomialFactors.lean](../Surreal/Algebra/RealClosedPolynomialFactors.lean); `Surreal.HahnSeries.exists_weighted_monomial_normalization`, `exists_monic_reduction`, `exists_monic_depressed_reduction` in [PolynomialNormalization.lean](../Surreal/HahnSeries/PolynomialNormalization.lean) | Generic field scaling preserves monicity and degree and supplies exact root pullbacks; the actual sign-field API now reuses it. In a divisible ordered abelian exponent group, an attained minimum of the finitely many weighted orders makes every coefficient nonnegative in valuation and retains a nonzero lower residue. The resulting monic residue has the same degree, retains the depressed coefficient, and is not a pure power. The exponent group needs no field structure or Archimedean hypothesis. Finite coprime factor extraction uses only an existing residue root; ordinary real-closed coefficients supply odd roots. **Proved** prerequisites for the full fixed-Hahn closedness constructions below. Build and axiom audit pass. |
| Global square roots in the real Hahn workspace of `found:sub:hahncomplex` | `Surreal.HahnSeries.leadingNormalized`, `orderTop_leadingNormalized_sub_one_pos`, `leadingMonomial_mul_leadingNormalized`, `exists_pos_square_root_of_coefficients`, `existsUnique_nonneg_square_root`, `hahnLexHasNonnegSquareRoots`, `isSquare_of_nonneg_lex` in [SquareRoots.lean](../Surreal/HahnSeries/SquareRoots.lean) | Every nonnegative lexicographic Hahn series has a unique nonnegative square root when the coefficient field has nonnegative square roots and the exponent group is divisible. Leading-term normalization gives one plus a positive-order error; the already constructed binomial half-power, a coefficient square root and a halved exponent give the exact root. Zero and pure monomials are included. This uses the weaker square-root interface and assumes no Hahn real closedness. **Proved** on the fixed Hahn carrier. Build and axiom audit pass. |
| Real and algebraic closedness clauses in `found:sub:hahncomplex`, `found:sub:localization`, `polynomial:prop:workspace` | `Surreal.HahnSeries.hahnCharZero` in [Characteristic.lean](../Surreal/HahnSeries/Characteristic.lean); `exists_root_of_monic_of_isAlgClosed`, `exists_root_of_isAlgClosed_coefficients`, `hahnIsAlgClosed` in [AlgebraicallyClosed.lean](../Surreal/HahnSeries/AlgebraicallyClosed.lean); `exists_isRoot_of_monic_odd_natDegree`, `exists_isRoot_of_odd_natDegree`, `exists_isRoot_of_odd_natDegree_lex`, `hahnLexIsRealClosed`, `hahnIsRealClosed` in [RealClosed.lean](../Surreal/HahnSeries/RealClosed.lean) | Over a divisible ordered abelian exponent group, Hahn fields with algebraically closed characteristic-zero coefficients are algebraically closed, and Hahn fields with ordered real-closed coefficients are real closed. The proofs translate and scale each polynomial, extract proper coprime residue factors, lift them using the constructed Hahn Hensel theorem, and induct on strictly smaller degree. Pure powers give explicit roots; monic normalization handles all nonconstant inputs. The real proof selects a proper odd-degree factor and combines odd roots with the constructed square roots. Characteristic zero transfers through the injective constant map. These are proved native `IsAlgClosed` and `IsRealClosed` instances, with no closure hypothesis on the Hahn field. [RealClosedReal.lean](../Surreal/Algebra/RealClosedReal.lean) supplies the ordinary real coefficient instance missing from the pinned Mathlib, using its square roots and intermediate value theorem; the default audit explicitly checks both ordinary real and complex Hahn instantiations. **Proved** for the fixed-Hahn closedness assertions; embedding arbitrary actual surreal data and constructing the normal-form bridge remain pending. Build and axiom audit pass. |
| Fixed complex-Hahn factorization in `polynomial:thm:fta`, `polynomial:eq:factorization`; root persistence in `found:thm:workspace`, `polynomial:prop:workspace`; finite-point image containment in `found:thm:finitepoints` | `Surreal.HahnSeries.complex_polynomial_splits`, `complex_polynomial_exists_root`, `complex_polynomial_factorization`, `complex_polynomial_roots_card`, `complex_polynomial_exists_unique_factorization`, `complex_polynomial_roots_map`, `complex_polynomial_root_mem_range`, `complex_finite_algebra_character_descends` in [PolynomialWorkspace.lean](../Surreal/HahnSeries/PolynomialWorkspace.lean) | Instantiates the existing finite algebra in the constructed complex Hahn field: all polynomials split in their original divisible workspace; nonconstant polynomials have roots; the scalar/multiset factorization is unique for nonzero inputs and has the exact degree count. Every extension preserves root locations and multiplicities. A character of a finite workspace algebra takes values in the original workspace even in a larger field. No additional splitting or closedness premise is assumed. **Proved** for these fixed-Hahn clauses; local algebra lengths, containment of actual surcomplex input data and the surreal interpretation remain separate obligations. Build and axiom audit pass. |
| Root-persistence clause of `found:thm:workspace` | `Surreal.FinitePolynomial.roots_map`, `root_mem_range`, `roots_map_of_isAlgClosed` | Roots and multiplicities of split polynomials under field extension. Small divisible exponent groups, their closed Hahn fields and support-compatible Hahn embeddings are constructed above. Containment of arbitrary actual surcomplex data and the infinite normal-form bridge remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Coefficientwise complexification in the proof of `polynomial:prop:workspace` | `Surreal.HahnSeries.complexifyHahnEquiv`, `coeff_complexifyToHahn`, `coeff_hahnToComplexify_re`, `coeff_hahnToComplexify_im`, `support_complexifyToHahn` in [HahnSeries/Complexify.lean](../Surreal/HahnSeries/Complexify.lean) | A ring equivalence between the quadratic extension of Hahn series over `R` and Hahn series with coefficients in `R[i]`, for any commutative ring `R`. Real and imaginary projection supports are contained in the original support, and the combined support is exactly their union. Native coefficient and conjugation results are mapped below. Closure and surreal workspace construction remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `K_Γ = F_Γ[i]` and conjugation-fixed-field identification in `polynomial:prop:workspace` | `Surreal.Complexify.complexEquiv` in [Algebra/ComplexNumbers.lean](../Surreal/Algebra/ComplexNumbers.lean); `Surreal.HahnSeries.conjugation_eq_self_iff_mem_range` in [Conjugation.lean](../Surreal/HahnSeries/Conjugation.lean); `realComplexHahnEquiv`, `complexConjugation_realComplexHahnEquiv`, `complexConjugation_eq_self_iff_mem_range`, `orderTop_complexConjugation`, `realHahnSubfieldEquiv`, `mem_realHahnSubfield_iff` in [HahnSeries/ComplexNumbers.lean](../Surreal/HahnSeries/ComplexNumbers.lean) | The quadratic algebra over native `ℝ` is ring-isomorphic to native `ℂ`, compatibly with scalar inclusion, `i`, and conjugation. Thus complex Hahn series are the quadratic extension of real Hahn series; the conjugation-fixed elements are precisely the injectively embedded real Hahn series. Conjugation preserves support and Hahn order. The generic fixed-image theorem assumes a characteristic-zero coefficient field; the ring statements allow ordered cancellative exponent monoids. For exponent groups, the real image is a bundled subfield, isomorphic to the real Hahn field and characterized by conjugation fixedness. Real/algebraic closedness of these Hahn fields is now constructed above for divisible exponents. The actual surreal embedding remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Image-containment clause of `found:thm:finitepoints` | `Surreal.FinitePolynomial.finite_algebra_character_descends` | A character of a finite algebra over an algebraically closed base takes values in that base. Local decomposition and base-change/local-length assertions remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `a:lem:neumann`, `a:rule:wordlength` | `Surreal.HahnSeries.neumann_add`, `finite_words_of_sum_eq`, `finite_nondecreasing_words_of_sum_eq`, `neumann_positive` in [Neumann.lean](../Surreal/HahnSeries/Neumann.lean) | **Proved** over an arbitrary ordered abelian group: well-ordered sumsets, finite pair-sum fibers, a well-ordered positive generated monoid, and finite fixed-sum word fibers across all lengths. The all-word version strengthens the requested nondecreasing-word statement. Uses Mathlib's partial well-order and Higman APIs. |
| Full finite-word support lemma `dyn:lem:neumann`; corrected combinatorial depth in `dyn:cor:ancestry` | `Surreal.HahnSeries.isPWO_add_positive_closure`, `finite_shifted_words_of_sum_eq`, `exists_shifted_word_length_bound`, `exists_shifted_nonempty_word_depth_bound`, finite contributing inputs/letters, `positiveMonomialShift`, `iterate_positiveMonomialShift_negative_monomial`, `no_input_independent_ancestry_depth` in [Ancestry.lean](../Surreal/HahnSeries/Ancestry.lean), together with [Neumann.lean](../Surreal/HahnSeries/Neumann.lean) | An arbitrary well-ordered input support plus the positive generated monoid is well ordered. At each output exponent, only finitely many input-exponent/word pairs contribute, so a finite depth bound exists depending on that input support. The earlier full word lemma supplies the unshifted part. The actual complex-linear shift on complex Hahn series proves `T^n(t^(-n)) = 1` and excludes every input-independent bound at output zero, checking the documented correction below. **Proved** for the support lemma, corrected combinatorial bounds and counterexample. The full operator-summability assertion remains pending. Build and axiom audit pass. |
| Constant-family specialization of `a:def:summable`, `a:rule:clauseii`; nonsummability part of `a:ex:notsummable` | `Surreal.HahnSeries.summable_constants_iff`, `hsum_constants`, `not_summable_constants_of_infinite`, `not_summable_geometric_constants` in [Constants.lean](../Surreal/HahnSeries/Constants.lean) | A family of constants is strongly summable exactly when its coefficient function has finite support. The nonzero constants `2⁻ⁿ` give a counterexample even though their support union is contained in `{0}`. Uses Mathlib's actual `SummableFamily`; ordinary analytic convergence and surreal interpretation are separate obligations. **Prerequisites proved**; build and axiom audit pass. |
| Regrouping and interchange assertions following `a:def:summable` | `Surreal.HahnSeries.restrict`, `regroup`, `coeff_hsum_fiber`, `coeff_regroup`, `hsum_regroup`, `hsum_fubini` in [Regroup.lean](../Surreal/HahnSeries/Regroup.lean) | Any index map regroups a jointly summable Hahn family into a summable family of fiber sums with unchanged total. Includes infinite fibers and double-sum interchange, with joint summability explicit throughout. Uses finite coefficient families rather than a topological convergence operation. The surreal interpretation remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Algebraic standard-part claims in `a:eq:st` and the following decomposition | `Surreal.HahnSeries.nonnegativeSubring`, `standardPart`, `standardPart_surjective`, `mem_infinitesimalIdeal`, `infinitesimalIdeal_isMaximal`, `residueEquiv`, `exists_unique_standardPart_decomposition` in [StandardPart.lean](../Surreal/HahnSeries/StandardPart.lean) | On the nonnegative-order Hahn subring over a coefficient field, coefficient-zero extraction is a surjective ring homomorphism with maximal positive-order kernel. The quotient is the coefficient field, and the constant-plus-positive-order decomposition is unique. Zero has order infinity and is included. The ordinary modulus-bounded surcomplex ring and its standard part are constructed above; identification of this Hahn coefficient map with actual standard part is proved above. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:reductionfactor` and its preceding root/coefficient assertions | `Surreal.HahnSeries.orderTop_nonneg_of_monic_root`, `orderTop_nonneg_of_monic_root_of_coeff_nonneg`, `coeff_orderTop_nonneg_of_monic_split_roots`, `coeff_orderTop_nonneg_multiset_prod`, `splits_nonnegative_of_splits`, `standardPart_factorization`, `roots_standardPart` in [PolynomialReduction.lean](../Surreal/HahnSeries/PolynomialReduction.lean) | Roots of monic polynomials with nonnegative-order coefficients have nonnegative order. The converse holds for split monic polynomials, including finite products. A monic polynomial over the nonnegative-order subring that splits in the Hahn field already splits in the subring. Standard part preserves the complete linear factorization and maps the root multiset, adding multiplicities when reductions coincide. Splitting is explicit in this general theorem; the proved closedness instance now supplies it over complex coefficients and divisible exponents. Identification with surreal modulus-boundedness remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Actual surcomplex root and reduction assertions in `polynomial:eq:reductionfactor` | `Surreal.Surcomplex.finiteSubring_integers`, `finite_of_integral`, `finite_of_monic_root`, `finite_of_monic_root_of_coeff_finite`, `coeff_finite_of_monic_split_roots`, `coeff_finite_multiset_prod`, `splits_finite_of_splits`, `standardPart_factorization`, `roots_standardPart`, `isRoot_standardPart` in [Surcomplex/PolynomialReduction.lean](../Surreal/Surcomplex/PolynomialReduction.lean) | Mathlib’s integrality theorem for valuation rings proves that every actual surcomplex root of a monic polynomial with finite coefficients is finite. Conversely, finite roots of a split monic polynomial give finite coefficients. Splitting in the actual ambient field descends to its finite ring, and the ordinary-complex standard-part map preserves the full linear factorization and root multiset, adding multiplicities at coincident reductions. Every finite root reduces to a root. **Proved** with the explicit splitting hypotheses shown; the unconditional splitting premise is now supplied by the actual surcomplex algebraic-closedness theorem above. Build and axiom audit pass. |
| Uniqueness and coprimeness clauses of `polynomial:thm:hensel` | `Surreal.FinitePolynomial.isCoprime_of_monic_reductions`, `monic_factorization_unique_of_reductions`, `monic_finite_factorization_unique_of_reductions` in [Algebra/PolynomialFactorUniqueness.lean](../Surreal/Algebra/PolynomialFactorUniqueness.lean); native standard-part specializations in [HahnSeries/PolynomialFactorUniqueness.lean](../Surreal/HahnSeries/PolynomialFactorUniqueness.lean) and [Surcomplex/PolynomialFactorUniqueness.lean](../Surreal/Surcomplex/PolynomialFactorUniqueness.lean) | Unit reflection of the residue homomorphism and monic preservation of resultant degrees lift coprimeness. Cross-coprimeness, divisibility and preserved degrees prove uniqueness of every finite monic factor family with the same pairwise coprime reductions, including empty families and constant factors. The hypothesis that the standard-part map reflects units is proved for both the nonnegative Hahn ring and the actual finite surcomplex ring. Candidates need no preassigned support monoid or formal-series presentation. **Proved** for these uniqueness and coprimeness clauses; factor existence and its support certificate remain separate. Build and axiom audit pass. |
| Univariate summability and ring-compatibility clauses of `a:cor:complexsub` | `Surreal.HahnSeries.evaluate`, `evaluate_X`, `summable_coeff_mul_powers`, `coeff_evaluate`, `coeff_zero_evaluate`, `summable_powers` in [Evaluation.lean](../Surreal/HahnSeries/Evaluation.lean) | Admissible evaluation reuses Mathlib `PowerSeries.heval` as an algebra homomorphism, with an explicit positive-`orderTop` proof and the actual coefficient-times-power term formula. Zero is included because its `orderTop` is infinity. Univariate composition is mapped separately below. Finite-variable evaluation is mapped below, and actual real/complex evaluation is proved above; differentiation remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Finite-variable summability and algebra-homomorphism clauses of `a:cor:complexsub`; support control for `polynomial:thm:hensel` | `Surreal.HahnSeries.summable_finite_products`, `mvPowerFamily`, `mvEvaluationFamily`, `summable_mv_coeff_mul_powers`, `finite_mv_coeff_support`, `isPWO_mv_support`, `mvEvaluate`, `coeff_mvEvaluate`, `coeff_zero_mvEvaluate`, order bounds, `support_mvEvaluate_subset_closure` in [MvEvaluation.lean](../Surreal/HahnSeries/MvEvaluation.lean) | Every formal power series in finitely many variables evaluates at positive-order Hahn inputs through an actual algebra homomorphism. Finite products of summable power families prove joint summability; regrouping the product by multiindex addition proves multiplication. Each Hahn coefficient receives finitely many contributions, and the support lies in the additive monoid generated by the input supports. Constant coefficients are preserved; all outputs have nonnegative order, and zero-constant inputs give positive order. Zero variables and arbitrary ordered cancellative exponent monoids are allowed; coefficient rings may have zero divisors. Finite-variable composition is mapped below, and actual real/complex evaluation is proved above; differentiation remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Univariate composition clause of `a:cor:complexsub` | `Surreal.HahnSeries.orderTop_evaluate_nonneg`, `orderTop_evaluate_pos_of_constantCoeff_zero`, `coeff_evaluate_eq_sum`, `evaluate_subst` in [Composition.lean](../Surreal/HahnSeries/Composition.lean) | Evaluation of arbitrary formal power series commutes with formal substitution when the inner series has zero constant coefficient and the Hahn argument has positive order. The evaluated inner series is itself proved admissible. Coefficientwise finite-support calculations justify the interchange, including zero inner series or argument. Finite-variable Hahn composition is now mapped below; actual real/complex composition is proved above; analytic coefficient-ring interpretations remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Finite-variable composition clause of `a:cor:complexsub` | `Surreal.HahnSeries.summable_mv_composition_coefficients`, `coeff_mvEvaluate_eq_sum`, `mvEvaluate_subst` in [MvComposition.lean](../Surreal/HahnSeries/MvComposition.lean) | Strong Hahn evaluation commutes with native multivariate formal substitution when all inner series have zero constant term and the finitely many Hahn arguments have positive order. Evaluated inner values are proved to have positive order. A constructed jointly summable double family and explicit finite coefficient fibers justify interchange; arbitrary outer coefficients and rings with zero divisors are allowed. No fine-topological continuity or convergence is assumed. **Proved** for this formal Hahn composition clause; actual real/complex composition is proved above; differentiation remains pending. Build and axiom audit pass. |
| `a:eq:geom` and formal remainder in `a:ex:geometric` | `Surreal.HahnSeries.geometric_mul`, `geometric_hsum`, `geometric_remainder` | The strongly summable power family has sum `(1-x)⁻¹`, with exact finite-sum remainder `x^(N+1)/(1-x)`, when `x` has positive order. The identity is generic Hahn algebra. Actual evaluation, remainder valuation, fine-topology nonconvergence and the explicitly named radius bound are proved above. **Prerequisites proved**; build and axiom audit pass. |
| Binomial specialization of `a:cor:complexsub`; root identity used in `b:ramification` and local trigonometric binomial expansions | `Surreal.HahnSeries.binomialTerms_apply`, `binomialPower_eq_hsum`, `orderTop_binomialPower_sub_one_pos`, `binomialPower_add`, `binomialPower_nat`, `binomialPower_rat_root`, `binomialPower_half_sq` in [Binomial.lean](../Surreal/HahnSeries/Binomial.lean); `pow_injective_near_one`, `binomialPower_rat_root_unique`, `exists_unique_root_near_one` in [BinomialRoots.lean](../Surreal/HahnSeries/BinomialRoots.lean) | The proof-gated binomial family has the actual terms `choose r n • x^n`, constant coefficient one, positive-order difference from one, and formal exponent-addition/natural-power laws. Rational exponents give an `m`th root of `1+x` for nonzero natural `m`. Over a characteristic-zero Hahn field, this is the unique root whose difference from one has positive order, using the geometric factor's nonzero standard part `m`. The positive ordered-root identification is mapped below. The actual binomial interpretation is proved above; ramification normal forms and analytic convergence remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Positive square-root branch in the local trigonometric binomial expansions | `Surreal.HahnSeries.lex_pos_of_sub_one_orderTop_pos`, `binomialPower_lex_pos`, `binomialPower_half_eq_of_nonneg_sq`, `exists_unique_nonneg_sqrt_one_add` in [BinomialOrder.lean](../Surreal/HahnSeries/BinomialOrder.lean) | Over any ordered coefficient field, every rational binomial power near one is positive in Mathlib's lexicographic Hahn order. The half-power is the unique nonnegative square root of `1+x` when `x` has positive order, including zero `x`. The constructed local root needs no real-closedness assumption. Global nonnegative Hahn square roots are now constructed above for divisible exponents. The actual positive square-root identification is proved above; analytic convergence remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `meas:lem:sumalgebra` (positivity clause); converse and positivity clauses of `meas:thm:atomic`; atomic cases of `meas:thm:atomic`(iv), `meas:prop:integration` and `meas:cor:cardinality` in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex) | `Surreal.HahnSeries.hsum_pos`, `hsum_nonneg`, `IsStrongHahnMeasure`, `atomicMeasure`, `coeff_atomicMeasure`, `atomicMeasure_singleton`, `atomicMeasure_iUnion`, `disjointFamily_apply`, `isStrongHahnMeasure_atomicMeasure`, `atomicMeasure_nonneg_iff`, `atomicMeasure_mono`, `atomicMeasure_regroup`, `isStrongHahnMeasure_pushforward`, `atomicIntegral` and its coefficient, linearity, indicator and positivity theorems, `setOf_ne_zero_eq_iUnion` in [StrongMeasure.lean](../Surreal/HahnSeries/StrongMeasure.lean) | A strong sum of lexicographically nonnegative Hahn series over any linearly ordered cancellative coefficient monoid is nonnegative, and positive when one summand is positive. `meas:def:strong` is formalized for arbitrary measurable spaces. A strongly summable family defines on all subsets a strong Hahn measure whose singleton masses are the given weights, additive on every set-indexed disjoint family through an explicit regrouping. It is positive exactly when all weights are nonnegative. Pushforwards are atomic with fiber masses, and the coefficientwise integral of an arbitrary scalar function is linear, agrees on indicators and is positive for positive data. **Proved** with arbitrary index sets and exponent orders; the forward direction of `meas:thm:atomic` is mapped in the atomicity row below. Build and axiom audit pass. |
| `prony:prop:prony`, `prony:eq:orthog`, `prony:prop:last`, and the exact identities `prony:eq:localeq` and `prony:eq:rootexact` of `prony:lem:localroots` in [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/article.tex) | `Surreal.Prony.moment`, `hankel`, `hankel_moment`, `det_hankel_moment`, `det_hankel_moment_ne_zero`, `momentFunctional_eq_sum_coeff`, `nodePoly`, `momentFunctional_nodePoly_mul`, `cofactor`, `momentFunctional_cofactor_mul`, `hankel_mulVec_lowCoeffs`, `nodePoly_eq_of_moment_eq`, `exists_perm_of_moment_eq`, `not_moment_eq_of_lt`, `eval_perturbed_eq`, `local_root_equation`, `local_root_mul`, `local_root_exact`, `momentLinear`, `hankel_mulVec_of_annihilates`, `monic_annihilator_unique`, `lastPerturbed`, `hankel_lastPerturbed`, `lastMomentPoly`, `momentLinear_lastMomentPoly_mul`, `lastMomentPoly_unique` in [PronyHankel.lean](../Surreal/Algebra/PronyHankel.lean) | Over an arbitrary field, the Hankel matrix of power moments is `Vᵀ diag(w) V`, with determinant `(∏ w_i)(∏_{i<j}(a_j-a_i))²`, nonzero for distinct nodes and nonzero weights. The node polynomial annihilates every polynomial multiple, and the cofactors are orthogonal with diagonal values `w_i Q_i(a_i)²`. Any `n`-node configuration, not assumed regular, sharing the first `2n` moments of a regular one is a permutation of it, nodes and weights alike; no configuration with fewer nodes shares the first `2n-1` moments. If only `m_{2n-1}` is perturbed by an arbitrary `e`, the Hankel matrix is unchanged and `P_e = P - e∑Q_i/(w_i Q_i(a_i)²)` is the unique monic annihilator of the perturbed moments, exactly and for every `e` (`prony:prop:last`, via Mathlib's Lagrange interpolation). A root `x` of a cofactor-coordinate perturbation away from the other nodes satisfies `prony:eq:localeq`, and `z = x-a_i` satisfies `z(1+∑_{j≠i} b_j/(a_i-a_j+z)) = -b_i`, which is `prony:eq:rootexact` when the bracket is nonzero. **Proved** for `prony:prop:prony`, `prony:eq:orthog` and `prony:prop:last`; the valuation localization in `prony:lem:localroots` (one root per ball, via `prony:lem:hensel`) and the remaining estimates are pending. Build and axiom audit pass. |
| Finite clauses of `herg:thm:negativeatom`, `herg:thm:quadrature` and `herg:thm:schur`; `herg:eq:badH`, `herg:eq:boundarynegative` in [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/article.tex) | `Surreal.Herglotz.toeplitz`, `negAtomMoment`, `toeplitz_negAtomMoment`, `toeplitz_negAtomMoment_mulVec_one`, `toeplitz_negAtomMoment_mulVec_of_sum_eq_zero`, `det_toeplitz_negAtomMoment`, `toeplitz_negAtomMoment_posDef`, `det_toeplitz_negAtomMoment_pos`, `hermForm_toeplitz_negAtomMoment`, `hermForm_toeplitz_negAtomMoment_pos`, `cayley_negAtomHerglotz`, `schur_step`, `abs_schurParam_lt_one`, `schurIterate_denominator_eq_zero`, `schurPole_mem_Ioo`, `one_sub_schurPole`, `negAtomHerglotz_one_sub`, `quadratureWeight_pos`, `sum_quadratureWeight`, `quadrature_moment` in [HerglotzNegativeAtom.lean](../Surreal/Algebra/HerglotzNegativeAtom.lean) | `T_N(c)=(1+ε)I-εJ`; the constant vector has eigenvalue `1-Nε`, the sum-zero hyperplane eigenvalue `1+ε`, and `det T_N(c)=(1+ε)^N(1-Nε)`. For `0 ≤ ε` and `Nε < 1` in any ordered field, both the real form and the Hermitian form over the complexification are positive definite; at a positive infinitesimal this holds for every ordinary `N`. The Cayley quotient (with `2` invertible) and every Schur iterate have the exact rational forms, with `abs α_n < 1` and poles in `(0,1)` at distance `ε/(1-(n-1)ε)` from `1`. The roots-of-unity quadrature has positive weights, total mass one and moments `-ε` for `0<n<M`. **Proved for these finite algebraic clauses**; the signed-measure representation and its uniqueness, weak-* convergence and `herg:thm:fejer` remain pending. Build and axiom audit pass. |
| Algebraic clauses of `markov:lem:resolvent`, `markov:thm:flag-realization` and `markov:lem:completion` in [Markov generators](surreal/markov-generators-at-every-scale/article.tex) | `Surreal.Markov.resolvent`, `inv_sub_inv`, `resolvent_mul_resolvent_eq`, `resolvent_commute`, `IsFlag`, `flagGenerator`, `resolvent_flagGenerator`, `flagGenerator_eq_abel`, `flagGenerator_mulVec_one`, `flagGenerator_offDiag_nonpos`, `resolvent_completion`, `completion_offDiag_neg` in [MarkovResolvent.lean](../Surreal/Algebra/MarkovResolvent.lean) | Over an arbitrary field, normalized resolvents satisfy `markov:eq:resolvent-identity` and commute. A flag with `P_iP_j=P_{max(i,j)}` gives the generator of `markov:eq:simple-inverse` with exactly the resolvent `markov:eq:simple-inverse-resolvent`. Stochastic flags give zero row sums, and the Abel-summed form `markov:eq:inverse-signs` makes off-diagonal entries nonpositive for nonnegative flags and `τ_1>⋯>τ_m>0`. The rank-one completion has the exact resolvent `markov:eq:completion-convex`, without commuting `𝟙ν` past `H`, and strictly negative off-diagonal entries. **Proved for these algebraic clauses**; residues, the shadows `markov:eq:same-scale`, `markov:eq:cross-scale` and `markov:eq:simple-inverse-shadow`, and the remaining hierarchy theorems are pending. Build and axiom audit pass. |
| `tail:lem:stabilization` and `tail:lem:multilinear` in [tail spans](surreal/tail-spans-and-differential-transcendence/article.tex) | `Surreal.TailSpan.deletedSpan`, `cofiniteSpan`, `exists_deletedSpan_eq_cofiniteSpan`, `finite_setOf_not_mem_cofiniteSpan`, `span_eq_cofiniteSpan_of_exceptions`, `multilinear_eq_zero_of_distinct`, `span_baseChange_eq_top`, `multilinear_baseChange_eq_zero` in [TailSpan.lean](../Surreal/Algebra/TailSpan.lean) | For an arbitrary family in a finite-dimensional space over any field, one finite deletion attains the cofinite span `W`, only finitely many members lie outside `W`, and after removing them every cofinite subfamily spans exactly `W`. A multilinear form vanishing on all tuples of pairwise distinct members of a family whose cofinite subfamilies span is zero, including for zero arguments and an empty index set. Spanning transfers to `K ⊗ W` through `Submodule.baseChange`, giving the source's scalar-extended form. **Proved** for both lemmas, with no countability or alphabet hypothesis. Build and axiom audit pass. |
| `wick:lem:dickson`, `wick:prop:hilbert`, `wick:prop:module` and `wick:lem:valCS` in [Wick summability](surcomplex/wick-summability-certificates/article.tex) | `Surreal.Wick.finite_setOf_minimal`, `exists_minimal_le`, `hilbertBasis`, `finite_hilbertBasis`, `mem_hilbertBasis_iff`, `mem_closure_hilbertBasis`, `fiber_eq_biUnion`, `finite_minimal_fiber`, `diag_pos_and_sq_lt`, `orderTop_add_le_of_sq_lt`, `valuation_cauchySchwarz` in [WickSemigroup.lean](../Surreal/Algebra/WickSemigroup.lean) | Dickson's lemma is Mathlib's well-quasi-order instance on `ℕ^ι`. For the nonnegative kernel of any additive map to an abelian group, which covers `Am = Dk`, the minimal nonzero elements are finite, are exactly the indecomposable elements, and generate the kernel; every fiber is the union of kernel translates by its finitely many minimal elements. A symmetric positive-definite matrix over an ordered field has positive diagonal and `C_ij² < C_ii C_jj`; over the lexicographic Hahn field this gives `v(C_ii)+v(C_jj) ≤ 2v(C_ij)` without divisibility of the exponent group. **Proved** for these four statements. Build and axiom audit pass. |
| Part (2) of `hol:lem:support` in [holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex), and `meas:lem:neumann` and `wick:lem:neumann` in [Wick summability](surcomplex/wick-summability-certificates/article.tex) and [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex); `meas:lem:labeled` in the latter | `Surreal.HahnSeries.isPWO_closure_of_pos`, `wordsWithSum`, `finite_wordsWithSum`, `finite_multisetsWithSum`, `wordProduct`, `exists_exponents_of_coeff_wordProduct_ne_zero`, `labeledWordFamily` in [NeumannWords.lean](../Surreal/HahnSeries/NeumannWords.lean) | For a partially well-ordered set of positive elements of a linearly ordered cancellative monoid, the generated monoid is partially well-ordered and each element has finitely many representations as an ordered word, hence as a multiset. The proof uses well-founded induction through finite antidiagonals and no Archimedean bound on word lengths. Products over all finite labeled index words of a strongly summable positive-order family form a strongly summable family. **Proved**. Build and axiom audit pass. |
| `meas:prop:products` in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex) | `Surreal.HahnSeries.finsetProductFamily`, `oneSubProduct`, `oneSubProduct_term`, `orderTop_oneSubProduct_sub_one_pos`, `isUnit_oneSubProduct`, `support_inv_one_sub_subset`, `ratioFamily`, `ratioFamily_id_apply` in [InfiniteProducts.lean](../Surreal/HahnSeries/InfiniteProducts.lean) | Finite-subset products of a strongly summable positive-order family are strongly summable, and the infinite product `U = ∏(1-q_n)` of equation (13) satisfies `U ∈ 1+𝔪` and is a unit. The ratios `a_i/(1-q_{g(i)})` of equation (14) are strongly summable for rows given by an arbitrary grouping map, which includes the source's finite rows and `q_n/(1-q_n)`. **Proved**; the coefficientwise finite-factor product identities used afterwards with (13), `meas:lem:recover` and `meas:thm:independent` remain pending. Build and axiom audit pass. |
| `meas:lem:boolean` in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex) | `Surreal.BooleanDisjoint.exists_disjoint_of_atomless_below`, `exists_pairwise_disjoint_ne_bot` in [BooleanDisjoint.lean](../Surreal/Algebra/BooleanDisjoint.lean) | Every infinite Boolean algebra has a sequence of pairwise disjoint nonzero elements: distinct atoms when there are infinitely many; otherwise the atoms' join is not the top (else every element would be the join of the atoms below it, making the algebra finite), and a strictly decreasing chain below its atomless complement gives disjoint differences. **Proved**. Build and axiom audit pass. |
| `meas:lem:scalar` and `meas:prop:coefficients` in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex) | `Surreal.HahnSeries.IsCountablySeparated`, `IsFinsumAdditive`, `measurableSet_singleton_of_separated`, `finite_setOf_singleton_ne_zero`, `finiteAtomic`, `HereditarilyNull`, `hereditarilyNull_iUnion`, `eq_zero_of_singleton_eq_zero`, `eq_finiteAtomic`, `finiteAtomic_unique`, `isFinsumAdditive_coeff`, `coeff_eq_finiteAtomic` in [ScalarAtomicity.lean](../Surreal/HahnSeries/ScalarAtomicity.lean) | A scalar set function whose disjoint measurable sequences have finitely many nonzero values summing to the value of the union is, on a countably separated space, the finite combination of its nonzero point masses, uniquely. No topology on the scalars is used. The proof replaces the quotient Boolean algebra by a bisection along the separating sets: hereditarily null measurable sets form a σ-ideal, only finitely many set-aside pieces can fail to be hereditarily null, and the chain intersection has at most one point. Every coefficient of a strong Hahn measure satisfies the hypothesis. **Proved** for both statements. Build and axiom audit pass. |
| `meas:lem:global` in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex) | `Surreal.Selection.supportedSum`, `exists_infinite_ne_zero` in [NonvanishingSelection.lean](../Surreal/Algebra/NonvanishingSelection.lean) | For finitely supported functionals each with a nonzero coefficient, some set inside the union of the supports makes infinitely many of them nonzero. The source's probabilistic argument is replaced by a deterministic one: pigeonhole when infinitely many nonzero supports lie in one finite set, and otherwise fresh points outside all earlier supports, included exactly when the earlier choices contribute zero. The index set need not be countable. **Proved**. Build and axiom audit pass. |
| Forward direction of `meas:thm:atomic` and `meas:cor:coefficient-test` in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex) | `Surreal.HahnSeries.globalSupport`, `HasAtomicCoefficients`, `hasAtomicCoefficients_of_exists`, `hasAtomicCoefficients_of_isStrongHahnMeasure`, `isWF_globalSupport`, `atomFamily`, `eq_atomicMeasure`, `globalSupport_eq_iUnion`, `isStrongHahnMeasure_of_hasAtomicCoefficients`, `isStrongHahnMeasure_iff` in [MeasureAtomicity.lean](../Surreal/HahnSeries/MeasureAtomicity.lean) | On a countably separated space, if every coefficient function is a finite combination of point masses, which holds for every strong Hahn measure, the global support is well ordered, the singleton masses form a strongly summable family, every measurable event mass is the strong sum of its singleton masses, and the global support is the union of the singleton supports. Such a set function is a strong Hahn measure, so the two conditions of `meas:cor:coefficient-test` are equivalent without any common-support assumption. **Proved** for `meas:thm:atomic`(i)–(iii) and `meas:cor:coefficient-test`; the uniqueness of the extension to all subsets in `meas:thm:atomic`(iv) and `meas:cor:shadow` are mapped in the shadow row below. Build and axiom audit pass. |
| `meas:thm:nullideal` (with `meas:eq:coef-measure`, `meas:eq:nullideal`, `meas:eq:null-criterion`, `meas:eq:control`) and `meas:cor:dominated` in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex); `herg:thm:nullideal` (with `herg:def:measure`, `herg:eq:nullideal`, `herg:eq:nullcriterion`, `herg:eq:control`, `herg:eq:ACcriterion`) and `herg:cor:twoscale` in [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/article.tex) | `Surreal.NullIdeal.coefSeries`, `nullIdeal`, `empty_mem_nullIdeal`, `mem_nullIdeal_of_subset`, `iUnion_mem_nullIdeal`, `nullIdeal_min`, `criterion_at_iff`, `criterion_of_nonneg`, `nonneg_of_criterion`, `tfae_nonneg`, `nonneg_iff_negPart`, `nonneg_iff_criterion`, `control`, `control_apply_eq_zero_iff`, `control_univ_le_one`, `isFiniteMeasure_control`, `control_of_isEmpty`, `mem_nullIdeal_iff_control`, `negPart_null_iff_absolutelyContinuous`, `exists_control`, `dominated`, `coefSeries_univ_eq_one`, `dominated_probability`, `twoScale`, `twoScale_measure` in [NullIdealPositivity.lean](../Surreal/HahnSeries/NullIdealPositivity.lean) | Setting: any measurable space, any linearly ordered exponent set (no group structure needed), and a well-ordered support of any cardinality. For the coefficientwise Hahn set function of finite real signed measures, three conditions are equivalent. (a) It is nonnegative on every measurable set. (b) Each coefficient is nonnegative on the sets that are null for all earlier total variations. (c) Each negative Jordan part vanishes on the σ-ideal `J_{<γ}`. Sufficiency is proved by well-founded induction below the least nonzero coefficient. The control measure `∑ w_i \|ν_{β_i}\|/(1+‖ν_{β_i}‖_TV)`, taken over an enumeration of the predecessors with any nonzero weights, has exactly `J_{<γ}` as its null sets, so the condition at `γ` becomes `ν_γ⁻ ≪ λ_{<γ}`. With the weights `2^{-j}` its mass is at most `1`, and it is zero when there are no predecessors. Dominated corrections are positive and vanish exactly on the `P_0`-null events; when normalized they form a coefficientwise Hahn probability. The two-scale measure `ν₀ + t^η ν₁` is positive if and only if `ν₀ ≥ 0` and `ν₁⁻ ≪ ν₀`, and `m + t^η ν ≥ 0` if and only if `ν⁻ ≪ m`, for any finite measure `m`. **Proved** for all four statements; the separate `herg:ex:uncountable` remains pending. Build and axiom audit pass. |
| `meas:cor:shadow`, `meas:cor:cardinality`, `meas:def:positive` (strong case), uniqueness and set-indexed additivity of the extension to all subsets in `meas:thm:atomic`(iv), and `meas:prop:integration`(i) for arbitrary strong measures in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex) | `Surreal.HahnSeries.isCountablySeparated_of_le`, `IsCountablySeparated.measurableSet_singleton`, `IsStrongHahnMeasure.preimage`, `IsStrongHahnMeasure.union`, `strongWeights`, `eq_atomicMeasure_strongWeights`, `preimage_eq_atomicMeasure_regroup`, `eq_atomicMeasure_of_le`, `existsUnique_isStrongHahnMeasure_top`, `iUnion_of_isStrongHahnMeasure_top`, `setOf_singleton_ne_zero_eq_biUnion`, `finite_setOf_singleton_coeff_ne_zero`, `countable_setOf_singleton_ne_zero`, `lift_mk_setOf_singleton_ne_zero_le`, `mk_setOf_singleton_ne_zero_le`, `IsStrongHahnProbability`, `coeff_eq_zero_of_neg_of_le_one`, `IsStrongHahnProbability.le_one`, `mem_Icc`, `coeff_eq_zero_of_neg`, `zero_le_orderTop`, `zero_le_orderTop_singleton`, `exists_finset_coeff_zero`, `shadow`, `exists_isProbabilityMeasure` in [StrongMeasureShadow.lean](../Surreal/HahnSeries/StrongMeasureShadow.lean) | On a countably separated space, a strong Hahn measure extends uniquely to a strong Hahn measure on all subsets. The extension is the strong sum of the point weights, and it is additive, with strong sums, on every set-indexed disjoint family. Uniqueness holds for every finer σ-algebra, because countable separation passes to finer σ-algebras. The pushforward along a measurable map is strong for every strong Hahn measure, with no separation hypothesis, and on a countably separated space it is the atomic measure of the fibre masses. The atomic set is the union, over the global support, of finite coefficient rows, so it is countable when the global support is and has cardinality at most `max(ℵ₀, \|S(μ)\|)`, with universe lifts. A strong Hahn probability over any linearly ordered additive group of coefficients with a `1` has event masses in `[0,1]` and no negative exponents, using finite additivity only. On a countably separated space, the constant coefficients of the point weights are positive exactly on a finite set, sum to `1`, and give the constant coefficient of every event mass. For real coefficients this is a finitely supported Mathlib probability measure. **Proved**, with the standard part read as the coefficient at exponent `0`, as in the source's definition on the valuation ring. Build and axiom audit pass. |
| `wick:thm:alternative` and `wick:eq:alternative` in [Wick summability](surcomplex/wick-summability-certificates/article.tex); `markov:lem:separation` in [Markov generators](surreal/markov-generators-at-every-scale/article.tex) | `Surreal.Alternative.Feasible`, `Obstruction`, `not_feasible_and_obstruction`, `obstruction_of_elim`, `feasible_of_elim`, `feasible_or_obstruction`, `strict_alternative`, `feasible_iff_not_obstruction`, `feasible_iff_forall_pos`, `not_feasible_not_obstruction_of_subsingleton`, `exists_rat_functional_pos` in [Algebra/StrictAlternative.lean](../Surreal/Algebra/StrictAlternative.lean) | Let `Γ` be a nonzero ordered `ℚ`-vector space, which is the Wick report's standing nonzero divisible ordered abelian group. Take a rational matrix with arbitrary finite row and column types and constants in `Γ`. Then exactly one of two things holds: some `p` has `Mp+b>0` in every row, or some nonzero `r ≥ 0` has `rᵀM=0` and `r·b≤0`. `wick:eq:alternative` is the equivalent universal form. Mutual exclusion needs no nontriviality. Existence genuinely fails over `Γ=0`. The proof is the source's Fourier–Motzkin elimination: it carries the nonnegative certificates and chooses the eliminated coordinate as a midpoint, as a one-sided bound shifted by a positive element, or as zero. For the separation lemma, `W` is a finite-dimensional `ℚ`-vector space with any partial order compatible with addition. There, finitely many strictly positive elements, possibly none, are all sent to positive rationals by one `ℚ`-linear functional. This proof applies the alternative over `ℚ` rather than the source's convex-hull and nearest-point argument. **Proved**; nothing is pending. Build and axiom audit pass. |
| `markov:lem:splitting`, including the canonical description by closed classes and the rank count, in [Markov generators](surreal/markov-generators-at-every-scale/article.tex) | `Surreal.StochasticIdempotent.exists_splitting`, `canonical_splitting`, `Reaches`, `IsClosedCommClass`, `classOf`, `closedClasses`, `mem_closedClasses_iff`, `splitU`, `splitV`, `splitU_mul_splitV`, `splitV_mul_splitU`, `splitU_nonneg`, `splitV_nonneg`, `sum_splitU`, `sum_splitV`, `vecMul_splitV`, `eq_splitV_of_stationary`, `splitV_pos`, `splitV_eq_zero`, `card_closedClasses`, `apply_eq_zero_of_transient`, `apply_eq_splitV`, `apply_eq_splitU_mul_splitV`, `splitU_apply_of_mem`, `apply_le_diag`, `transGen_iff` in [StochasticIdempotent.lean](../Surreal/Algebra/StochasticIdempotent.lean) | Over any linearly ordered field, a square row-stochastic idempotent `P` factors as `P=UV` with entrywise nonnegative row-stochastic `U : n × rank P`, `V : rank P × n` and `VU=I`. The canonical factors are indexed by a finite set of classes, proved equal to the closed communicating classes of the graph of positive entries (defined literally through reachability). Each row of `V` is its class's stationary probability vector extended by zero. It is positive exactly on the class and is the unique stationary vector of mass one supported there. `U_{iC}=∑_{k∈C}P_{ik}` is the mass row `i` assigns to `C`. The number of classes equals `rank P`. The structural facts of the source proof are also proved. Transient columns vanish, so `T_0=0`. Each closed block is `𝟙ν_C` with `ν_C>0`. Every row, transient ones included, restricted to `C` is `U_{iC}ν_C`. At class states the rows of `U` are coordinate rows. The limit argument `T_0^m→0` is replaced by a maximum principle for the `P`-harmonic columns. **Proved**. Build and axiom audit pass. |
| `epd:def:orderunit` and `epd:lem:ideal` in [expanding polynomial dynamics](surcomplex/expanding-polynomial-dynamics/article.tex) | `Surreal.ScaleIdeal.IsOrderUnit`, `not_isOrderUnit_iff`, `scaleSubgroup`, `ordConnected_scaleSubgroup`, `scaleSubgroup_le`, `scaleSubgroup_eq_top_iff`, `errorSubgroup`, `errorIdeal`, `image_errorIdeal`, `image_mul_errorSubgroup`, `span_singleton_mul_errorIdeal`, `mem_errorSubgroup_iff_forall_pow`, `coe_errorSubgroup_eq_iInter`, `errorIdeal_eq_iInf_span_pow`, `errorSubgroup_eq_bot_iff`, `errorIdeal_eq_bot_iff`, `errorSubgroup_ne_bot`, `exists_ball_subset`, `exists_ball_mem_iff`, `exists_ball_subset_of_mem`, `exists_ball_subset_compl_of_not_mem`, `coarseValuationSubring`, `coarseValuation_le_iff`, `coarseValuation_eq_iff`, `nonunits_coarseValuationSubring`, `image_maximalIdeal_coarseValuationSubring`, `mem_maximalIdeal_coarseValuationSubring_iff`, `mem_errorSubgroup_iff_eq_zero_or` in [ScaleIdeal.lean](../Surreal/HahnSeries/ScaleIdeal.lean) | The field `k` is arbitrary and `Γ` is any linearly ordered abelian group, with no `Γ ≠ 0` and no divisibility. `H_κ` is a convex subgroup that lies in every convex subgroup containing `κ`, and for `κ > 0` it is all of `Γ` exactly when `κ` is an order unit. `I_κ` is an additive subgroup of `K` and an ideal of `O`. `q I_κ = I_κ` whenever `v(q) = κ ≥ 0`, both as sets and as ideals. For `κ > 0`, `I_κ = ⋂ₙ qⁿO` as sets and as an infimum of principal ideals, and `I_κ = 0` exactly when `κ` is an order unit. Otherwise `I_κ` is nonzero and clopen. Mathlib has no topology on Hahn series, so clopenness is stated through the valuation balls `{y : v(y - x) > η}`, with one radius for all centers. The coarsened valuation is realized as a Mathlib `ValuationSubring` whose valuation compares `v` modulo `H_κ`; no explicit order isomorphism between its value group and `Γ/H_κ` is built. Its nonunits and its maximal ideal are exactly `I_κ`, and `h ∈ I_κ` iff `h = 0` or `v(h)` exceeds every element of `H_κ`. **Proved**; no clause is pending. Build and axiom audit pass. |
| `hol:def:entire` (univariate domain and entireness), `hol:def:orderunit` (definition only), `hol:lem:nonincreasing`, `hol:lem:escape` with `hol:eq:escapeineq`, `hol:thm:escapeexclusion` with `hol:eq:boundincrements`, `hol:cor:boundedcost`, `hol:prop:expdomain` with `hol:eq:expdomain`, and the exact-boundary remark after it in [holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex) | `Surreal.Holonomic.StronglySummable`, `stronglySummable_iff`, `stronglySummable_iff_isWF`, `strongDomain`, `IsStronglyEntire`, `IsOrderUnit`, `not_stronglySummable_of_antitone_order`, `not_stronglySummable_of_order_succ_le`, `exists_escape_step`, `exists_escape_chain`, `not_stronglySummable_of_escape`, `not_mem_strongDomain_of_escape`, `eq_zero_of_stronglySummable_escape`, `eq_zero_of_boundedCost`, `single_neg_witness`, `eq_zero_of_boundedCost_single`, `stronglySummable_single_mul_pow_iff`, `formalExp`, `coeff_formalExp`, `natCast_add_one_eq_single`, `coeff_succ_formalExp_mul`, `derivative_formalExp`, `coeff_formalExp_mul_pow`, `mem_strongDomain_formalExp_iff`, `strongDomain_formalExp`, `not_mem_strongDomain_formalExp_iff`, `expRecCoeff`, `formalExp_recurrence`, `expRecCoeff_zero_ne_zero`, `escapeBound_formalExp_iff`, `not_mem_strongDomain_formalExp_iff_escapeBound` in [EscapeChain.lean](../Surreal/HahnSeries/EscapeChain.lean) | The value group is any linearly ordered abelian group; divisibility is not assumed. Strong summability means the family is the terms of a `SummableFamily`, which is the same as a well-ordered support union with finite incidence at each exponent. A family is not strongly summable if nonzero members at distinct indices have nonincreasing orders; other members may vanish. Take `hol:eq:generalrecurrence` over any coefficient semiring without zero divisors, with `c_0(n) ≠ 0`, and one nonzero `a_{n_0}` with `n_0 ≥ N`. Then `s ≥ 1`, and there is an infinite chain with jumps in `{1,…,s}` along which `hol:eq:escapeineq` holds. If the weak bound `hol:eq:boundincrements` holds at `x ≠ 0`, then `(a_n x^n)` is not strongly summable; equivalently, strong summability forces `a_n = 0` for all `n ≥ N`. A single bound `B` gives the same conclusion for every `x ≠ 0` with `v(x) ≤ -max(B,0)`, and every `t^{-δ}` with `δ ≥ max(B,0)` is such an `x`. Over any field of characteristic zero, `D_zE_η = t^ηE_η` and `Dom(E_η) = {0} ∪ {x ≠ 0 : v(x) > -η}`. For the first-order recurrence of `E_η`, the escape bound holds exactly on the closed complement, and the escape criterion itself proves the exclusion. **Proved**; `hol:cor:periodic`, parts (1) and (3) of `hol:lem:support` (part (2) is mapped above), `hol:lem:certificate`, `hol:prop:closure` and the `d`-variable clause of `hol:def:entire` remain pending. Build and axiom audit pass. |
| `trigonometry:eq:orthogonalityfinite`; `trigonometry:thm:fourier` with `trigonometry:eq:fourierinverse`, `trigonometry:eq:parsevalsample` and both identities of `trigonometry:eq:dft` in [surcomplex trigonometry](surcomplex/trigonometry/article.tex) | `Surreal.FiniteFourier.cast_ne_zero_of_isPrimitiveRoot`, `sum_zpow_mul`, `orthogonality`, `sum_zpow_mul_sub`, `laurentEval`, `laurentEval_mul_zpow_sample`, `fourier_inversion`, `star_laurentEval`, `parseval_samples`, `dft`, `dft_inversion`, `dft_parseval`, `zeta`, `zeta_eq_ofComplex`, `isPrimitiveRoot_zeta`, `modulus_zeta`, `ne_zero_of_modulus_eq_one`, `star_eq_inv_of_modulus_eq_one`, `ofReal_modulus_sq`, `surcomplex_orthogonality`, `surcomplex_fourier_inversion`, `surcomplex_parseval_samples`, `surcomplex_dft_inversion`, `surcomplex_dft_parseval` in [FiniteFourier.lean](../Surreal/Surcomplex/FiniteFourier.lean) | The generic results hold over any field containing a primitive `M`-th root of unity `ζ`. No characteristic assumption is needed, because such a root forces `(M : K) ≠ 0`. `(1/M)∑_{j<M} ζ^{jk}` is `1` if `M ∣ k` and `0` otherwise, for every integer `k`. For `T(u)=∑_{k=-N}^{N} c_k u^k` and `M > 2N`, the samples `T(u₀ζ^j)` recover every `c_k` with `\|k\| ≤ N` at any nonzero base point. Given a conjugation with `star ζ = ζ⁻¹` and `star u₀ = u₀⁻¹`, the sampled Parseval identity holds, and arbitrary `z_0,…,z_{M-1}` satisfy DFT inversion and Parseval. On the actual `SC`, `ζ = cis(2π/M)` is the finite phase of the real angle `2π/M`; it equals the embedded `exp(2πi/M)` and is a primitive `M`-th root. The coefficients and samples are arbitrary surcomplex numbers, and `u₀ ∈ 𝕋(No)` is surreal modulus one. Both Parseval identities hold in `No` for the surreal-valued modulus squared. **Proved**, with inversion for every nonzero base point. Pending: the positivity remark after the theorem and the later coefficientwise-integration and positivity subsections of the same section. Build and axiom audit pass. |
| `meas:lem:recover` (with `meas:eq:first-error`, `meas:eq:survival` and `meas:eq:recover`) and `meas:def:summability` in [hahn-valued measures](surreal/hahn-valued-measures-and-probability/article.tex) | `Surreal.FirstError.StronglySummable`, `stronglySummable_iff`, `supportSubring`, `stronglySummable_of_support_subset_fibre`, `stronglySummable_of_support_subset`, `rowSum`, `survival`, `firstError`, `firstErrorMass`, `survival_eq`, `survival_mem`, `firstErrorMass_mem`, `orderTop_firstError_pos`, `orderTop_firstErrorMass_pos`, `eq_firstError_mul_hsum_powers`, `firstError_smul_powers_apply`, `hsum_firstError_smul_powers`, `stronglySummable_iff_firstError`, `stronglySummable_firstError_mul_pow`, `eq_firstError_mul_inv` in [FirstErrorRecovery.lean](../Surreal/HahnSeries/FirstErrorRecovery.lean) | Rare entries are indexed by `Σ n, J n`, with finitely many `j` at each level. Levels start at `0`, so products and sums over `k < n` run over `Finset.range n`. A family is strongly summable when it is the family of members of a Mathlib `SummableFamily`. This is equivalent to the two clauses of `meas:def:summability`, with a partially well-ordered union of supports, which means well ordered for linearly ordered exponents. For entries of positive order (zero allowed), `(p_{n,j})` is strongly summable exactly when the first-error masses `(h_{n,j})` are. The survival identity `∏_{k<n}(1-q_k) = 1 - H_{<n}` needs no hypothesis. The recovery identity `p_{n,j} = ∑ˢ_m h_{n,j}H_{<n}^m` holds, and over a coefficient field this equals `h_{n,j}(1-H_{<n})⁻¹`. When `(h_{n,j})` is strongly summable, the double family `(h_{n,j}H_{<n}^m)_{(n,j),m}` is strongly summable, with no bound on `n` or `m`. Instead of the source's labelled-word expansion, the proof uses a support-domination criterion through Neumann's lemma. Everything except the inverse form holds over any commutative coefficient ring and any linearly ordered cancellative exponent monoid. **Proved**; the event masses `μ(B_{n,a}) = h_{n,a}` and the projection away from `J` in the necessity half of `meas:thm:independent` remain pending. Build and axiom audit pass. |
| `tail:lem:difference`, including `tail:eq:diffidentity` and the value form used in `tail:prop:orbit`, in [tail spans](surreal/tail-spans-and-differential-transcendence/article.tex) | `Surreal.TailSpan.translate`, `eval_translate`, `diffOp`, `dirDeriv`, `dirDeriv_eq_sum_pderiv`, `diffOp_step`, `iterDiff`, `iterDirDeriv`, `iterDiff_zero`, `iterDirDeriv_zero`, `iterDiff_eq_iterDirDeriv`, `iterDirDeriv_homogeneousComponent_eq_C`, `iterDiff_eq_C`, `eval_iterDiff`, `alternatingSum_eq_coeff_iterDirDeriv`, `dirDeriv_commute`, `iterDirDeriv_comp_perm`, `pow_dirDeriv_of_isHomogeneous`, `alternatingSum_diagonal_eq`, `polarization`, `polarization_apply`, `polarization_zero`, `iterDirDeriv_eq_C_factorial_mul_polarization`, `iterDiff_eq_factorial_mul_polarization`, `polarization_comp_perm`, `polarization_diagonal`, `eq_polarization_of_symmetric`, `alternatingSum_eq_factorial_mul_polarization`, `homogeneousComponent_eq_zero_of_polarization_eq_zero`, `mixedDifference_of_charZero` in [MixedDifference.lean](../Surreal/Algebra/MixedDifference.lean) | Over any commutative ring, in any set of variables, and for `P` of total degree at most `D`, `Δ_{u_1}⋯Δ_{u_D}P = D_{u_1}⋯D_{u_D}P_D`. This is a constant polynomial, and at every base point `x` the alternating sum of `P(x + ∑_{j∈J} u_j)` over `J ⊆ {1,…,D}` equals that constant. Over a field with `D! ≠ 0`, which the source's characteristic zero implies, the `D`-linear form `T = (D!)⁻¹ D_{u_1}⋯D_{u_D}P_D` is symmetric. It satisfies `T(x,…,x) = P_D(x)` at every point and is the unique symmetric form that does. It gives `D_{u_1}⋯D_{u_D}P_D = D! T(u_1,…,u_D)` and the value form with `D! T`. For `D = 0` the operator products are the identity and `T = P_0`. Over an infinite field, `T = 0` forces `P_D = 0`. A degree-lowering induction replaces the source's Taylor expansion, and the identity `P_D(X) = T(X,…,X)` is stated pointwise, which determines `P_D` over the source's infinite field. **Proved**; `tail:prop:orbit` itself remains pending. Build and axiom audit pass. |
| `prony:eq:numerators`, `prony:lem:pade` with `prony:eq:pade`, `prony:lem:cross` with `prony:eq:cross`, and `prony:eq:Dvalues` in [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/article.tex) | `Surreal.Prony.momentSeriesPoly`, `padeNumerator`, `coeff_mul_momentSeriesPoly`, `degree_padeNumerator_lt`, `degree_pade_remainder_lt`, `coeff_reflect_padeNumerator_mul_inv`, `nodePoly_mul_momentSeriesPoly_moment`, `degree_sum_C_mul_cofactor_lt`, `padeNumerator_moment_nodePoly`, `degree_nodePoly_pade_remainder_lt`, `eq_sum_C_mul_cofactor`, `eq_nodePoly_of_isRoot`, `moment_eq_of_padeNumerator_eq`, `moment_padeResidues`, `cross_numerator_eq`, `degree_cross_lt`, `cross_numerator_nodePoly`, `eval_cross_cofactor`, `le_valuation_coeff_cross`, `le_orderTop_coeff_cross`, `le_orderTop_coeff_cross_nodePoly` in [PronyPade.lean](../Surreal/Algebra/PronyPade.lean) | The work is over an arbitrary field, with the Laurent series in `X⁻¹` cleared of denominators: `momentSeriesPoly N m = X^N ∑_{k<N} m_k X^{-k-1}`, and `[·]_+` is the quotient `/ₘ X^N`. Both numerators have degree `< n`. For every configuration, the unperturbed numerator is `A = ∑ w_i Q_i`, with no need for distinct nodes. If `L̂(P̂ X^r) = 0` for `r < n` and `deg P̂ ≤ n`, then `deg(P̂ · momentSeriesPoly (2n) m̂ - X^{2n} Â) < n`. For monic `P̂` of degree `n` this is equivalent to `prony:eq:pade`. The expansion at infinity is also proved literally in `K[[Y]]`, `Y = X⁻¹`, through reflected polynomials. If `P̂` is monic of degree `n` with `n` distinct roots `â_i`, the residues `Â(â_i)/P̂'(â_i)` realize `m̂_0, …, m̂_{2n-1}`. Let `P, P̂` have degree at most `n`, and let their numerators satisfy the polynomial Padé identities. Then `D = Â P - A P̂` is the polynomial part of `P P̂ ∑_{k<2n} ε_k X^{-k-1}`, so `deg D < 2n`. If `P, P̂` are integral and `v(ε_k) ≥ κ` for `k < 2n`, every coefficient of `D` has valuation `≥ κ`. This holds for any additive valuation, and in particular for `orderTop` on `R((t^Γ))`, with `R` any field and `Γ` any ordered abelian group. It is also stated in the source configuration `P = ∏(X - a_i)`, `A = ∑ w_i Q_i`. Monicity is not needed in `prony:lem:cross`. In cofactor coordinates `P̂ = P + ∑ b_j Q_j`, `D(a_i) = -w_i Q_i(a_i)² b_i = -u_i` for every `Â`. **Proved**; the weight estimate `prony:lem:weight` and the reconstruction assertions of `prony:thm:main` remain pending. Build and axiom audit pass. |
| `def:sigma-derivation` with `eq:sigma-leibniz` and `eq:twisted`; `thm:sigma-derivation` (both forms, `eq:uniform-output`), `prop:valued-amplification`, `cor:detector` (`eq:detector`), `thm:derivation-valued` (both forms, `eq:loss-bound`) and `cor:no-contraction` in [exponential automorphism rigidity](surreal/exponential-automorphism-rigidity/article.tex) | `Surreal.SigmaDerivation.IsSigmaDerivation`, `isSigmaDerivation_displacement`, `isSigmaDerivation_derivation`, `IsSigmaDerivation.toDerivation`, `IsSigmaDerivation.coe_toDerivation`, `min_le_valuation_mul`, `valuation_lt_or_valuation_lt`, `exists_valuation_neg`, `exists_valuation_mul_lt`, `exists_valuation_ne_zero`, `exists_valuation_lt_of_surjective`, `exists_valuation_lt_valuation`, `exists_valuation_lt`, `eq_zero_of_forall_le`, `IsSigmaDerivation.eq_zero`, `IsSigmaDerivation.exists_valuation_lt`, `eq_id_of_displacement_eq_zero`, `exists_displacement_lt_valuation`, `exists_displacement_lt`, `eq_id_of_detector`, `derivation_eq_zero_of_loss`, `exists_loss_lt`, `not_forall_le`, `not_forall_lt`, `smul_ne_zero_and_comp`, `not_forall_le_mul`, `not_forall_lt_mul` in [Algebra/SigmaDerivation.lean](../Surreal/Algebra/SigmaDerivation.lean) | The results hold on any field of any characteristic with an additive valuation `v` into `WithTop Γ`, where `Γ` is a linearly ordered abelian group of any rank. Nontriviality (`∃ x ≠ 0, v x ≠ 0`) and surjectivity onto `Γ` are explicit hypotheses wherever the source states them, and `σ` is never assumed to preserve `v`. The displacement `σ x - x` of a unital endomorphism is a `σ`-derivation, and ordinary derivations over any base ring are exactly the `id`-derivations. A `σ`-derivation whose output values are all `≥ β` for one `β` vanishes, and a nonzero one has output values below every `β`. The core argument needs only the twisted Leibniz rule for arbitrary maps `σ`, `δ` and a nontrivial `v`, which gives coinitiality in the value group `v(Kˣ)`. Coinitiality of the values of `v` in `Γ` can replace surjectivity, but surjectivity cannot simply be dropped: a nonzero bounded derivation exists when the image is `{0}×ℤ` in lexicographic `ℤ×ℤ`. The displacement values of a nonidentity endomorphism are coinitial in `v(Kˣ)` without surjectivity, and in `Γ` when `v` is surjective. The detector takes `E` to be a group homomorphism `(K,+) → (Kˣ,·)` and reads `E x ∈ 𝒪ᵥˣ` as `v (E x) = 0`. The loss theorem holds for any derivation over any base ring and any nowhere-vanishing `E`, and its second form reads `v(∂(E x)) < v(E x) + γ`. All four no-contraction assertions are proved, including those for `c∂` with `c ≠ 0`. **Proved** for these clauses. The ordered-field results `lem:amplify`, `cor:bounded-displacement`, `prop:sigma-witness`, `lem:derivation-amplify` and `thm:derivation` remain pending, as do the convex-valuation and exponential theorems and the surreal instantiations of `cor:detector` (via `prop:finite-log`) and `thm:derivation-valued` (via the Berarducci–Mantova derivation). Build and axiom audit pass. |
| `tate:node:lem:isometry` (`tate:node:eq:isometry`), with the vector valuation `𝐯` of `tate:node:sec:metric`, in [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/article.tex) | `Surreal.ChartIsometry.vecOrderTop_mvEvaluate_sub`, `isometry_of_det_ne_zero`, `vecOrderTop`, `le_vecOrderTop_iff`, `vecOrderTop_le`, `vecOrderTop_of_isEmpty`, `linearPart`, `nonlinearPart`, `coeff_nonlinearPart_zero`, `coeff_nonlinearPart_single`, `mvEvaluate_eq_linear_add_nonlinear`, `mvEvaluate_sub_eq`, `vecOrderTop_smul_sum`, `vecOrderTop_le_vecOrderTop_smul_sum`, `add_le_orderTop_mvEvaluate_nonlinearPart_sub`, `add_le_orderTop_prod_pow_sub`, `add_le_orderTop_prod_map_sub`, `card_nsmul_le_orderTop_prod_map`, `two_le_card_toMultiset`, `prod_pow_eq_prod_map_toMultiset`, `le_orderTop_hsum`, `le_orderTop_finset_sum` in [ChartIsometry.lean](../Surreal/HahnSeries/ChartIsometry.lean) | Let `A = (A_i)` be a family of formal power series whose linear part `L_A` (entry `(i,j)` is the coefficient of `Z_j` in `A_i`) is invertible. Strong Hahn evaluation of `A` at vectors `a, b` of positive-order Hahn series then satisfies `𝐯(A(a)−A(b)) = 𝐯(a−b)`, where `𝐯(w) = min_j v(w_j)` and `v(0) = ⊤`. The case `a = b`, zero coordinates and zero variables are all included. The coefficients may lie in any commutative ring with `L_A` a unit, so neither a field nor characteristic zero is used. `Γ` may be any linearly ordered cancellative commutative monoid, and the variables may be indexed by any finite type. No zero-constant-term hypothesis is needed, because the constant terms cancel. `isometry_of_det_ne_zero` is the source's setting: a field, an ordered abelian group, `Fin d` variables and `det L_A ≠ 0`. Every nonlinear monomial difference has order at least `𝐯(a−b)+ε`, and the proof bounds the strong sum term by term using this. It does not use the source's formal factorization `N(a)−N(b)=C(a,b)(a−b)`. An invertible constant matrix preserves `𝐯`. **Proved**; no clause of the lemma is pending. The node-chart consequence `tate:node:cor:bidisk` is not formalized: it also needs the node chart and `tate:node:lem:implicit`. Build and axiom audit pass. |
| `ihs:lem:neumann` with `ihs:eq:neumann`; `ihs:hh:thm:smooth` with `ihs:hh:eq:constres`, `ihs:hh:eq:inversesmooth`, `ihs:hh:eq:smoothsolution` in [infinite-dimensional Hahn spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex) | `Surreal.InfiniteSpectral.mulRight`, `hsum_mulRight`, `pow_finite_co_support_of_semiring`, `ringPowers`, `hsum_ringPowers_eq_one_add_mul`, `mul_hsum_ringPowers_comm`, `one_sub_mul_hsum_ringPowers`, `hsum_ringPowers_mul_one_sub`, `neumannFamily`, `one_add_mul_hsum_neumannFamily`, `hsum_neumannFamily_mul_one_add`, `support_hsum_neumannFamily_subset`, `isUnit_one_add_of_orderTop_pos`, `inv_one_add_eq_hsum_neumannFamily`, `neumann`, `shiftResolvent`, `coeff_shiftResolvent`, `shiftResolvent_eq_const_coeff`, `inverseSmoothFamily`, `inverseSmoothFamily_apply_eq_smul`, `shiftResolvent_hsum_inverseSmoothFamily`, `shiftResolvent_injective`, `mem_iInf_range_pow_iff`, `exists_shiftResolvent_eq_const_iff`, `eq_hsum_of_shiftResolvent_eq_const`, `inverseSmooth` in [NoncommutativeNeumann.lean](../Surreal/HahnSeries/NoncommutativeNeumann.lean) | Take any ring, possibly noncommutative, and exponents in a linearly ordered cancellative monoid. If `0 < orderTop E` (which includes `E = 0`), the powers `(-E)^n` form a strongly summable family. Its sum is a two-sided inverse of `1 + E`, equal to the unit inverse and supported in the additive monoid generated by `supp E`. Mathlib's commutative-only summability of powers is reproved, and the right identity uses only associativity, via `x·H = H·x`. Now take an injective endomorphism `S` of any module over a semiring, `η > 0` in a partially ordered abelian group, and constant data `f`. Then `(S - t^η)y = f` has a solution in `HahnModule Γ k V` exactly when `f ∈ Ran S^m` for every `m ≥ 1`. `S - t^η` is injective and the preimages `S^(-n-1)f` are unique. Every solution is the strong sum of the terms `t^(nη) S^(-n-1)f` and is supported in `{nη}`. **Proved** for both statements, at or above the source's generality. The analytic example `ihs:hh:ex:smoothD` and the corollaries `ihs:cor:evaluate` and `ihs:cor:binomial` remain pending. Build and axiom audit pass. |
| Half-angle, sum-to-product, product-to-sum and remaining double-angle clauses of `trigonometry:thm:identities`; the tangent-addition, sum-to-product and product-to-sum consequences displayed after it, including `trigonometry:eq:chebyshev`, in [surcomplex trigonometry](surcomplex/trigonometry/article.tex) | `Surreal.Surcomplex.eq_of_chebyshev_recurrence`, `finiteCos_zsmul_add_one`, `finiteSin_zsmul_add_one`, `chebyshev_T_eval_finiteCos`, `chebyshev_U_eval_finiteCos_mul_finiteSin`, `finiteSin_zsmul_eq_mul_chebyshev_U`, `finiteCos_two_mul_eq_cos_sq`, `finiteCos_two_mul_eq_sin_sq`, `finiteCos_sq_eq`, `finiteSin_sq_eq`, `finiteHalf`, `val_finiteHalf`, `finiteHalf_add_finiteHalf`, `two_mul_finiteHalf`, `eq_finiteHalf_iff`, `finiteHalf_add_add_finiteHalf_sub`, `finiteHalf_add_sub_finiteHalf_sub`, `finiteCos_finiteHalf_sq`, `finiteSin_finiteHalf_sq`, `finiteTan`, `finiteTan_zero`, `finiteTan_neg`, `finiteTan_add`, `finiteTan_sub`, `finiteTan_two_mul`, `finiteTan_eq_finiteSin_two_mul_div`, `finiteTan_eq_one_sub_finiteCos_two_mul_div`, `finiteTan_sq_eq`, `finiteTan_finiteHalf_eq_finiteSin_div`, `finiteTan_finiteHalf_eq_one_sub_finiteCos_div`, `finiteTan_finiteHalf_sq`, `two_mul_finiteSin_mul_finiteSin`, `two_mul_finiteCos_mul_finiteCos`, `two_mul_finiteSin_mul_finiteCos`, `two_mul_finiteCos_mul_finiteSin`, `finiteSin_add_finiteSin`, `finiteSin_sub_finiteSin`, `finiteCos_add_finiteCos`, `finiteCos_sub_finiteCos` in [FiniteTrigonometryIdentities.lean](../Surreal/Surcomplex/FiniteTrigonometryIdentities.lean) | Setting: the phase-coordinate sine and cosine on the whole finite subring `O_R`. The half angle `θ/2` is formed inside `O_R`, and it is the unique finite angle whose double is `θ`. The following hold: `cos 2θ = 2cos²θ − 1 = 1 − 2sin²θ` and power reduction; `cos²(θ/2) = (1+cos θ)/2` and `sin²(θ/2) = (1−cos θ)/2`; `tan(θ/2) = sin θ/(1+cos θ) = (1−cos θ)/sin θ` and `tan²(θ/2) = (1−cos θ)/(1+cos θ)`; all four sum-to-product and all four product-to-sum identities; and tangent addition, subtraction and doubling. Quotients use `x/0 = 0`. With that convention the half-angle tangent formulas need no hypothesis, and tangent addition needs only `cos α ≠ 0` and `cos β ≠ 0`. Both are stronger than the source's nonzero-denominator restriction. `cos(nα) = T_n(cos α)` and `sin(nα) = sin α U_{n−1}(cos α)` hold for every integer `n`, using Mathlib's ℤ-indexed Chebyshev polynomials. Their initial values and three-term recurrence are the source's, so the source's `n ≥ 1` is included. The proof is uniqueness for the shared recurrence over any commutative ring. **Proved for these identities and `trigonometry:eq:chebyshev`**. Still pending: the derivative clauses `(sin)' = cos`, `(cos)' = −sin` and `(cis)' = i cis`, and the identification with the Taylor sums `trigonometry:eq:sinfinite`/`cosfinite`. Build and axiom audit pass. |
| `wick:prop:quarticH` with the incidence relations and `s`-parametrization stated before it, the mixed model `wick:eq:mixedmodel` with its weights and obstruction, and the (ii)⟺(iii) clause of `wick:thm:main` in [Wick summability](surcomplex/wick-summability-certificates/article.tex) | `Surreal.Wick.countWeight`, `countWeight_apply`, `forall_kernel_pos_iff_forall_hilbertBasis_pos`, `quarticIncidence`, `quarticIncidence_eq_zero_iff`, `quarticIncidence_eq_zero_iff_exists`, `quarticH₁`, `quarticH₂`, `quarticH₃`, `quarticH₄`, `quarticIncidence_quarticH₁`, `quarticIncidence_quarticH₂`, `quarticIncidence_quarticH₃`, `quarticIncidence_quarticH₄`, `exists_eq_quarticH_combination`, `exists_quarticH_le`, `eq_quarticH_of_le`, `hilbertBasis_quarticIncidence`, `quarticWeight`, `quarticWeight_quarticH₁`, `quarticWeight_quarticH₂`, `quarticWeight_quarticH₃`, `quarticWeight_quarticH₄`, `two_nsmul_quarticWeight_quarticH₃`, `forall_hilbertBasis_quarticWeight_pos_iff`, `forall_kernel_quarticWeight_pos_iff`, `quartic_tests_irredundant`, `mixedModel_weights`, `mixedModel_obstruction`, `mixedModel_not_criterion`, `mixedModel_valuations`, `mixedModel_weights_rat` in [WickQuartic.lean](../Surreal/Algebra/WickQuartic.lean) | For `P = g₁x⁴ + g₂y⁴` with `C₁₁, C₁₂, C₂₂ ≠ 0`, the incidence map `Am - Dk` has nonnegative kernel `S`. It is cut out by `4m₁ = 2k₁₁ + k₁₂` and `4m₂ = 2k₂₂ + k₁₂`, equivalently by `k₁₂ = 2s`, `k₁₁ = 2m₁ - s`, `k₂₂ = 2m₂ - s` with `s ≤ 2min(m₁, m₂)`. The Hilbert basis of `S`, meaning its minimal nonzero elements, is exactly `{h₁, h₂, h₃, h₄}`. Every element of `S` is `a h₁ + b h₂ + c h₃ + d h₄` with `c ≤ 1`, as in the source proof. For weight data in any linearly ordered cancellative commutative monoid, `2w₃ = w₁ + w₂ + w₄`. Positivity on the Hilbert basis, and equally on all of `S∖{0}`, is equivalent to `w₁ > 0`, `w₂ > 0`, `w₄ > 0`. The equivalence of these two criteria holds for the kernel of any count map on `ℕ^ι` with `ι` finite. Over any nonzero ordered abelian group, the report's standing `Γ ≠ {0}`, each of the three tests fails for some data satisfying the other two, with `c₁₁ = c₂₂ = 0`. For `C = [[t², 1], [1, t²]]` and `g₁ = g₂ = t⁻¹`, with `t` the monomial of exponent `ε`, the Hahn valuations are `-ε`, `2ε` and `0`, and the weights are `3ε, 3ε, 2ε, -2ε`. In `ℂ((t^ℚ))` with `ε = 1`, the weights computed from the actual orders are `3, 3, 2, -2`. For `ε > 0`, `h₄` is the only Hilbert basis element of nonpositive weight. **Proved** as a statement about criteria (ii) and (iii) of `wick:thm:main`. The following remain pending: the link to strong summability of the Wick atoms, which is `wick:thm:main` (i); the offending atoms `(4n)!/(n!)² t^{-2n}` and their descending exponents; the admissibility of each quartic interaction alone; connectedness and cyclic amplification; the positivity of the displayed coefficients against regrouping; and `det C = t⁴ - 1` with the failure of positive definiteness. Build and axiom audit pass. |
| `epd:prop:branches` with `epd:eq:branch-metric` and `epd:eq:forward-metric`, for the family `epd:eq:polynomial` including its remark that `P` has degree `d` and unit leading coefficient, in [expanding polynomial dynamics](surcomplex/expanding-polynomial-dynamics/article.tex) | `Surreal.BranchMetric.orderTop_eq_zero_of_standardPart_ne_zero`, `standardPart_eq_zero_of_orderTop_pos`, `exists_divided_difference`, `orderTop_eval_sub_eval`, `existsUnique_eval_eq`, `SimpleResidueRoot`, `SimpleResidueRoot.existsUnique`, `branch`, `standardPart_branch`, `eval_branch`, `eq_branch`, `orderTop_branch_sub`, `forwardMap`, `forwardMap_coe`, `orderTop_forwardMap_sub_add`, `orderTop_forwardMap_sub`, `forwardMap_branch`, `branch_injective`, `residuePolynomial`, `perturbedPolynomial`, `residuePolynomial_ne_zero`, `natDegree_residuePolynomial`, `isRoot_residuePolynomial`, `eval_derivative_residuePolynomial_ne_zero`, `map_perturbedPolynomial`, `natDegree_perturbedPolynomial_le`, `isUnit_leadingCoeff_of_natDegree_le`, `natDegree_perturbedPolynomial`, `isUnit_leadingCoeff_perturbedPolynomial`, `simpleResidueRoot_perturbedPolynomial`, `branches` in [BranchMetric.lean](../Surreal/HahnSeries/BranchMetric.lean) | The field `k` is arbitrary and `Γ` is any linearly ordered abelian group. `Γ ≠ 0` is not assumed, divisibility is not assumed, and `d ≥ 2` is not used. The setting is `K = k⟦Γ⟧` with `v = orderTop` (so `v(0) = ⊤`), `O = nonnegativeSubring` and `st = standardPart`. `P = P₀ + ∑_{j ≤ d} e_j X^j`, where `P₀ = a_d ∏(X - c_i)` has its coefficients embedded as constants, `a_d ≠ 0`, the `c_i` are distinct and `e_j ∈ 𝔪`. Also `q ∈ 𝔪 \ {0}` and `F = q⁻¹P` on `K`. For each `i`, `branches` proves three things. Every `w ∈ O` has a unique `y ∈ O` with `st y = c_i` and `P(y) = qw`. The defined branch `Φ_i` satisfies `v(Φ_i(w) - Φ_i(z)) = v(q) + v(w - z)`. For `x, y ∈ O` of residue `c_i`, `v(F(x) - F(y)) = v(x - y) - v(q)` in `WithTop Γ`, and equal inputs give `⊤`. The generic lemmas need only a unit leading coefficient and a simple residue root. The divided-difference identity `v(P(x) - P(y)) = v(x - y)` needs only `P̄'(c) ≠ 0`. The branch metric allows `q = 0`, and the forward metric holds for every nonzero `q ∈ K`. `P` has degree `d` and a unit leading coefficient. `F(Φ_i(w)) = w`, so each branch is injective. Existence comes from the Hahn simple-root lift, not from the source's route through `epd:lem:formalbranch` and `epd:lem:evaluation`, which remain separate obligations. The remark that points of different pieces differ by valuation `0` is not formalized. **Proved**; no clause is pending. Build and axiom audit pass. |
| `herg:lem:leadingvector` and the finite-matrix clauses of `herg:thm:saturation` in [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/article.tex) | `Surreal.Herglotz.twistedForm`, `exists_single_mul_leading`, `map_single_one_of_coeff`, `map_C_of_coeff`, `orderTop_nonneg_of_coeff`, `twistedForm_single_mul`, `twistedForm_nonneg_coeff_zero`, `twistedForm_map_eq`, `twistedForm_leading`, `toLex_single_one_pos`, `toLex_pos_of_coeff_zero`, `leadingVector_real`, `hahnHermForm`, `conjugationHom`, `embedRealSeries_single_one`, `exists_embedRealSeries_pos`, `leadingVector`, `orderTop_toeplitz_nonneg`, `coeff_zero_toeplitz`, `toeplitz_hermitian`, `toeplitz_perturbation_pos`, `re_sum_star_delta_pos`, `toeplitz_saturation_pos`, `conjugation_single_one`, `toeplitz_saturation_pos_single`, `circleMoment`, `integrable_zpow_of_ae_norm_eq_one`, `star_circleMoment`, `norm_sq_sum_eq`, `sum_star_circleMoment`, `circleMoment_re_pos`, `toeplitz_circleMoment_posDef`, `complexConjugationHom`, `complexConjugation_complexConjugation`, `complexHermForm`, `complexRealEmbedding_single_one`, `exists_complexRealEmbedding_pos`, `leadingVector_complex`, `leadingVector_posDef`, `complex_toeplitz_perturbation_pos`, `complex_re_sum_star_delta_pos`, `complex_toeplitz_saturation_pos`, `complexConjugation_single_one`, `complex_toeplitz_saturation_pos_single`, `toeplitz_measure_perturbation_pos` in [LeadingVectorTest.lean](../Surreal/HahnSeries/LeadingVectorTest.lean) | Setting: any ordered abelian value group; no divisibility is used. If `A ∈ M_n(O_Γ)` is Hermitian over `ℂ((t^Γ))` and `st A` is positive definite (as `Matrix.PosDef`, or only `Re(x*(st A)x) > 0` for ordinary `x ≠ 0`), then `u*Au` is a strictly positive element of `ℝ((t^Γ))` for every nonzero Hahn vector `u`. The same holds over `R[i]((t^Γ))` for any ordered field `R`, and for real quadratic forms `uᵀAu` over `R((t^Γ))` with no symmetry assumed. The proof is the source's reduction `u = t^β w` with `st w ≠ 0`, done once for any coefficientwise ring endomorphism. For ordinary conjugate-symmetric `b` with no growth condition (the normalization `b_0 = 0` is not needed) and `ε = t^η`, `η > 0`, or any conjugation-fixed `ε` of positive valuation, `T_N(δ + εb)` is strictly positive against all Hahn vectors for every `N`. The Fourier moments `c_n = ∫ ζ^{-n} dμ` of a finite positive measure on the unit circle with infinite support are conjugate symmetric and have positive definite Toeplitz matrices. They stay strictly Toeplitz-positive under every entrywise positive-valuation, conjugate-symmetric perturbation. The algebraic form holds for any ordinary conjugate-symmetric moments with positive definite `T_N`, over `ℂ` and over `R[i]`. **Proved for `herg:lem:leadingvector` and the finite-matrix clauses of `herg:thm:saturation`**; the finite-completion clause of `herg:thm:saturation`, that every finite prefix is represented by the positive coefficientwise Hahn probability measure `(1+εq_N)m`, remains pending. Build and axiom audit pass. |

## Dependency order

1. **Size guards and finite algebra (Layer A).** First prove the unrestricted
   bound/cut contradictions (`found:prop:allcuts`) for an irreflexive relation.
   Define complexification of a commutative ring with multiplication
   `(a,b)(c,d) = (ac-bd, ad+bc)`, its scalar embedding, `i`, conjugation and norm
   square. Prove coordinate identities, involution, norm multiplicativity and
   Gram's identity before introducing order. Ordered-field positivity then
   justifies inverses; real closedness is an additional prerequisite for square
   roots and algebraic closedness. Source anchors: `found:eq:pairmul`,
   `found:eq:conj`, `found:eq:pairinv`, `found:prop:complex`, `found:eq:gram`,
   `found:eq:rationalcircle`, `trigonometry:eq:dotcross`, and
   `trigonometry:eq:gram`. The full `found:prop:complex` also asserts real-closed
   and class-coded conclusions; coordinate algebra alone does not complete it.
2. **Ordered algebra and finite polynomial consequences.** Establish the rational
   unit-circle parametrization and reusable finite linear/polynomial algebra.
   Factorization needs algebraic closedness; norm geometry needs the appropriate
   ordered/real-closed input. Early polynomial targets include
   `polynomial:thm:fta` and `polynomial:thm:crt`, followed by the finite-algebra
   descent theorem `found:thm:finitepoints`. Keep generic proofs separate from
   their surreal specializations.
3. **Set-sized Hahn support and evaluation (Layer B).** Prove well-ordering and
   local finiteness for admissible support families, support-preserving sums,
   positive-support geometric/binomial series, and admissible substitution.
   Then define standard part and Taylor lifting with recentering. Initial
   anchors include `polynomial:lem:support`, `trigonometry:lem:support`,
   `found:prop:positive`, and `found:cor:fixeddomain`.
4. **Coefficient rings and coherent functions (Layer C).** Give separate types
   to the four coefficient-ring conventions in the document map. Establish
   coefficientwise differentiation/integration and support-controlled
   composition, then local division/preparation, finite deformations, and
   residue duality. The analytic-geometry ring table must be checked before
   transporting any theorem between these types. Follow with contours and
   Stokes, global divisors, and the remaining polynomial/trigonometric results.
5. **Universe-indexed surreal construction and bridge (Layer D, independent
   foundational track).** Construct or import a checked numeric-game/sign
   development, with birthdays and a visible size bound. Prove field and order
   laws, real closedness, normal forms, monomials, and compatibility of admissible
   sums. Then prove `found:thm:workspace`. The eight surreal reports branch here:
   graph results need game representations; birthday and broadcast results
   need sign/ordinal arithmetic; evaluation and genetic-gap results need their
   specified supports or differentiation semantics. The plan's two tracks allow
   local Hahn mathematics to proceed before this bridge is finished.
   The [infinite normal-form bridge note](NORMAL_FORM_BRIDGE.md) records the
   verified upstream APIs, the canonical order isomorphism and inverse
   extraction and arithmetic, actual closedness, small real strong sums and exponent
   coherence, and the remaining Taylor and universe-coherence obligations.
   Approximation alone does not give uniqueness or arithmetic compatibility.
6. **Topology and further structure (Layer E).** Define the intended fine
   topology over the actual carrier and prove small-index discreteness alongside
   the larger-index counterexample. Prove finite-angle lifting, distinguish
   derivative notions, and supply any real exponential/global character as
   separate proved structures. Only after a universe-coherent/class
   interpretation is established can full-class all-scale rigidity and its
   consequences be claimed.

This is a dependency order, not a promise to process reports in file order.
A substantial theorem should be split into its simplest necessary lemmas while
retaining an explicit obligation for every conclusion of the source theorem.

Both inputs to Mathlib's `IsRealClosed.of_linearOrderedField` are now proved
for actual sign surreals: genetic nonnegative square roots and odd-degree
roots transported from a small divisible Hahn coefficient workspace.
Actual sign-field standard part, Conway monomials and weighted finite
coefficient scaling are now constructed. General finite-family coprime
factor linearization is a proved equivalence, using Mathlib’s Sylvester map
for the binary inverse. Translation to monic depressed form, the
actual polynomial scaling and reduction, and the ordinary-real coprime
factorization with a proper odd-degree factor are now constructed. The
binary lift in arbitrarily many formal parameters is now constructed as an actual
polynomial factorization over power series, with uniqueness, coprimeness and
exact degrees. Evaluation at finitely many positive-order Hahn inputs is a
proved algebra homomorphism with an explicit support certificate.
These constructions now give full finite-family, support-controlled coprime
factor lifting in arbitrary ordered Hahn fields, including the documented
common support monoid and unrestricted uniqueness. The ordered field
normal-form bridge and small-workspace localization transfer the resulting
Hahn odd-degree roots to actual surreals. Localizing both coordinates also
transfers complex Hahn roots to actual surcomplex numbers. Small real and complex strong
sums are now defined through their canonical coefficients and agree with
workspace evaluation. Univariate and finite-variable formal substitution are proved.
Recentered complex analytic germs and their sum/product laws are constructed;
fine differentiation is proved at zero and ordinary centers, with general
re-expansion, composition and multivariable analytic lifting still pending.
Conway's normalization and factor-lifting route is in
[*On Numbers and Games*, Theorems 23–28, pp. 40–42](https://kyl.neocities.org/books/%5BTEC%20CON%5D%20on%20numbers%20and%20games.pdf);
the universal ordered-field embedding there uses real closedness and cannot
be used circularly to obtain these roots. The finite-parameter strong-evaluation
bridge is now proved for ordinary coefficients; the remaining analytic
operation and nonordinary-center derivative correspondences are separate. Small-index convergence in the native fine topology
cannot replace strong Hahn summability.

## Soundness boundaries that must survive translation

- **Permitted cuts:** a type in one universe cannot fill cuts indexed by its
  whole own carrier. Smaller-index cut data must remain explicit. The abstract
  obstruction does not by itself construct legitimate surreal cuts or prove
  `found:lem:bounds` for surreal numbers.
- **Complex multiplication:** the default product ring on `F × F` has the
  wrong multiplication and identity. Use the actual quadratic extension or a
  dedicated structure; see `found:rem:productring`.
- **Class versus workspace:** proving a theorem for a fixed Hahn field is useful
  but does not supply a universal field of all surreal numbers. Workspace
  localization and preservation of the operations used need separate proofs.
- **Two near-mirror series:** `found:ex:rescaling` uses coefficients `t^(-n²)`
  and fails evaluation at every nonzero argument in the fixed rational value
  group; `found:ex:internal` uses `t^(n²)` and is nonpolynomial despite internal
  all-scale coherence. Full-class rigidity cannot be specialized to a fixed
  value group without its missing dominating-scale hypothesis.
- **Strong sums:** well-ordered support and finite coefficient contributions
  are both required. Formal identities are not topological limits. Taylor
  lifting at `r + ε` uses the Taylor series centered at `r`, not unrestricted
  Maclaurin substitution (`found:rem:recentering`).
- **Different analytic categories:** radius-free coefficient germs, a fixed
  ordinary domain, common-domain germs, and formal coefficient series are
  distinct rings. The analysis merge records inequivalent function classes and
  inequivalent residues; a common name does not authorize a common definition.
- **Different geometries:** Hahn valuation and ordered modulus have distinct
  root and contour statements. A contour representing a residue series is an
  extra theorem, not the definition of the series functional.
- **Topology and size:** small-set discreteness (`found:thm:discrete`) coexists
  with a larger-index nonconstant convergent net (`found:ex:largerindex`). Do not
  assert eventual constancy for arbitrary index types or silently introduce an
  ordinary metric for the fine topology (`found:lem:nometric`).
- **Overlapping birthday results:** the two Gonshor reports prove the same
  inequality on different domains, neither containing the other. The shared
  `R[[ω⁻¹]]` case can reuse a proof once equivalence is established, but both
  domain statements remain obligations.
- **Independent proof notions:** fine derivative, formal power-series germ,
  Hahn-coherent datum and scalar-field derivation must retain separate types
  and explicit comparison theorems.

## Canonical report inventory

`T`, `L`, `P`, `C` mean literal `theorem`, `lemma`, `proposition` and
`corollary` environments; examples, computations, assessments and other
custom environments are not included. Paths below identify all 44 main texts
present in the repository, including the two whose source is not named
`article.tex`. The reader map lists all of them; the typeset catalogue still
covers the 40 reports preceding the placement of `5fe7f8d`. The four newly
placed sources are indexed as drafts awaiting assembly and review.
The four reports and expanded sections from batch 19 are indexed here, but
remain pending unless a precise implementation mapping below states otherwise.

| Main report source | T | L | P | C | Total |
|---|---:|---:|---:|---:|---:|
| [foundations-and-computation/computable-surreals/article.tex](foundations-and-computation/computable-surreals/article.tex) | 24 | 5 | 21 | 6 | 56 |
| [foundations-and-computation/computer-algebra/article.tex](foundations-and-computation/computer-algebra/article.tex) | 4 | 0 | 8 | 2 | 14 |
| [foundations-and-computation/foundations/article.tex](foundations-and-computation/foundations/article.tex) | 3 | 2 | 16 | 2 | 23 |
| [physics/surreal-scalars-and-spacetime/article.tex](physics/surreal-scalars-and-spacetime/article.tex) | 4 | 1 | 11 | 3 | 19 |
| [surcomplex/analysis/article.tex](surcomplex/analysis/article.tex) | 57 | 10 | 24 | 26 | 117 |
| [surcomplex/analytic-geometry/article.tex](surcomplex/analytic-geometry/article.tex) | 38 | 18 | 16 | 14 | 86 |
| [surcomplex/contours-and-stokes/article.tex](surcomplex/contours-and-stokes/article.tex) | 26 | 11 | 12 | 5 | 54 |
| [surcomplex/differential-equations/article.tex](surcomplex/differential-equations/article.tex) | 64 | 37 | 35 | 39 | 175 |
| [surcomplex/dynamics-and-normal-forms/article.tex](surcomplex/dynamics-and-normal-forms/article.tex) | 49 | 35 | 37 | 28 | 149 |
| [surcomplex/entire-functions-at-arbitrary-rank/article.tex](surcomplex/entire-functions-at-arbitrary-rank/article.tex) | 34 | 23 | 14 | 29 | 100 |
| [surcomplex/expanding-polynomial-dynamics/article.tex](surcomplex/expanding-polynomial-dynamics/article.tex) | 10 | 3 | 4 | 8 | 25 |
| [surcomplex/finite-deformations/article.tex](surcomplex/finite-deformations/article.tex) | 23 | 10 | 6 | 13 | 52 |
| [surcomplex/global-divisors/article.tex](surcomplex/global-divisors/article.tex) | 17 | 13 | 15 | 12 | 57 |
| [surcomplex/hahn-herglotz-positivity/article.tex](surcomplex/hahn-herglotz-positivity/article.tex) | 12 | 2 | 2 | 4 | 20 |
| [surcomplex/hahn-tate-uniformization/article.tex](surcomplex/hahn-tate-uniformization/article.tex) | 25 | 19 | 10 | 16 | 70 |
| [surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex](surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex) | 11 | 15 | 11 | 14 | 51 |
| [surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex](surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex) | 33 | 20 | 19 | 21 | 93 |
| [surcomplex/nonabelian-support/article.tex](surcomplex/nonabelian-support/article.tex) | 24 | 16 | 15 | 19 | 74 |
| [surcomplex/polynomial-algebra/article.tex](surcomplex/polynomial-algebra/article.tex) | 28 | 6 | 9 | 14 | 57 |
| [surcomplex/prony-reconstruction-at-surreal-scales/article.tex](surcomplex/prony-reconstruction-at-surreal-scales/article.tex) | 2 | 7 | 5 | 3 | 17 |
| [surcomplex/rank-one-berkovich/article.tex](surcomplex/rank-one-berkovich/article.tex) | 9 | 2 | 11 | 6 | 28 |
| [surcomplex/spectral-theory/article.tex](surcomplex/spectral-theory/article.tex) | 30 | 16 | 13 | 18 | 77 |
| [surcomplex/trigonometry/article.tex](surcomplex/trigonometry/article.tex) | 39 | 4 | 11 | 10 | 64 |
| [surcomplex/wick-summability-certificates/article.tex](surcomplex/wick-summability-certificates/article.tex) | 5 | 7 | 7 | 4 | 23 |
| [surquaternions/surquaternions/article.tex](surquaternions/surquaternions/article.tex) | 27 | 4 | 15 | 2 | 48 |
| [surreal/broadcast-sum-of-surreal-sequences/article.tex](surreal/broadcast-sum-of-surreal-sequences/article.tex) | 7 | 9 | 1 | 5 | 22 |
| [surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex](surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex) | 15 | 13 | 7 | 4 | 39 |
| [surreal/exponential-automorphism-rigidity/article.tex](surreal/exponential-automorphism-rigidity/article.tex) | 15 | 6 | 9 | 11 | 41 |
| [surreal/gamma-functions/article.tex](surreal/gamma-functions/article.tex) | 11 | 7 | 6 | 2 | 26 |
| [surreal/genetic-gaps-and-primitives/article.tex](surreal/genetic-gaps-and-primitives/article.tex) | 7 | 3 | 4 | 1 | 15 |
| [surreal/gonshor-laurent-birthdays/article.tex](surreal/gonshor-laurent-birthdays/article.tex) | 5 | 8 | 0 | 5 | 18 |
| [surreal/gonshor-product-birthdays/surreal_product_birthdays.tex](surreal/gonshor-product-birthdays/surreal_product_birthdays.tex) | 3 | 4 | 5 | 2 | 14 |
| [surreal/hahn-evaluation-at-omega/article.tex](surreal/hahn-evaluation-at-omega/article.tex) | 7 | 9 | 5 | 2 | 23 |
| [surreal/hahn-valued-measures-and-probability/article.tex](surreal/hahn-valued-measures-and-probability/article.tex) | 19 | 14 | 8 | 18 | 59 |
| [surreal/markov-generators-at-every-scale/article.tex](surreal/markov-generators-at-every-scale/article.tex) | 9 | 5 | 3 | 3 | 20 |
| [surreal/tail-spans-and-differential-transcendence/article.tex](surreal/tail-spans-and-differential-transcendence/article.tex) | 8 | 8 | 4 | 1 | 21 |
| [surcomplex/three-duals-of-hahn-vector-spaces/article.tex](surcomplex/three-duals-of-hahn-vector-spaces/article.tex) | 16 | 4 | 5 | 4 | 29 |
| [surcomplex/hidden-negative-hermitian-directions/article.tex](surcomplex/hidden-negative-hermitian-directions/article.tex) | 10 | 4 | 4 | 6 | 24 |
| [surreal/transcendence-over-bounded-support/article.tex](surreal/transcendence-over-bounded-support/article.tex) | 9 | 8 | 3 | 10 | 30 |
| [surreal/matrix-scaling-at-surreal-scales/article.tex](surreal/matrix-scaling-at-surreal-scales/article.tex) | 7 | 3 | 2 | 4 | 16 |
| [surcomplex/surcomplex-field-automorphisms/article.tex](surcomplex/surcomplex-field-automorphisms/article.tex) | 16 | 3 | 6 | 1 | 26 |
| [surreal/euclidean-three-space/article.tex](surreal/euclidean-three-space/article.tex) | 14 | 0 | 2 | 0 | 16 |
| [surreal/finite-surreal-probability/article.tex](surreal/finite-surreal-probability/article.tex) | 15 | 2 | 7 | 1 | 25 |
| [surreal/vector-and-tensor-fields/article.tex](surreal/vector-and-tensor-fields/article.tex) | 8 | 1 | 6 | 2 | 17 |
| **Total** | 799 | 397 | 434 | 400 | **2030** |

The earlier refresh from `796f8d4` through `1f6d6b8` added four reports and
expanded an existing one.
Historically archived manuscripts are counted independently of their merged reports;
these counts assert no equivalence or additional independent results.

| New or expanded report | Added main-report statements | New preserved manuscripts | Standard environments in those manuscripts |
|---|---:|---:|---:|
| [Surreal scalars and spacetime](physics/surreal-scalars-and-spacetime/article.tex) | 19 | 3 | 20 |
| [Dynamics and normal forms](surcomplex/dynamics-and-normal-forms/article.tex) | 101 | 6 | 115 |
| [Nonabelian support](surcomplex/nonabelian-support/article.tex) | 45 | 2 | 43 |
| [Surquaternions](surquaternions/surquaternions/article.tex) | 48 | 2 | 65 |
| [Contours and Stokes: untransformed Leray cycles](surcomplex/contours-and-stokes/article.tex) | 19 | 1 | 21 |
| **Added** | **232** | **14** | **264** |

The refresh from `1f6d6b8` to `608dd23` adds three reports and expands five.
All added obligations are **pending unless explicitly mapped in the proof
ledger**. The newly archived first spectral manuscript overlaps the earlier
main report; its 29 environments are counted as preserved source material,
not as 29 new main-report statements.

| New or expanded report | Added main-report statements | New preserved manuscripts | Standard environments in those manuscripts |
|---|---:|---:|---:|
| [Analytic geometry: corona obstruction and spectral fibres](surcomplex/analytic-geometry/article.tex) | 33 | 1 | 33 |
| [Differential equations: Hermitian spectral–integral classification](surcomplex/differential-equations/article.tex) | 25 | 1 | 26 |
| [Dynamics: small divisors and resonance flags](surcomplex/dynamics-and-normal-forms/article.tex) | 16 | 1 | 17 |
| [Entire functions at arbitrary rank](surcomplex/entire-functions-at-arbitrary-rank/article.tex) | 47 | 2 | 59 |
| [Global divisors: compact-curve Picard classification](surcomplex/global-divisors/article.tex) | 20 | 1 | 21 |
| [Spectral theory: determinantal ramification and descent](surcomplex/spectral-theory/article.tex) | 29 | 2 | 61 |
| [Exponential automorphism rigidity](surreal/exponential-automorphism-rigidity/article.tex) | 26 | 0 | 0 |
| [Gamma functions](surreal/gamma-functions/article.tex) | 26 | 1 | 26 |
| **Added** | **222** | **9** | **243** |

The 40 manuscripts present before the earlier refresh contained 1075 standard
environments; the 54 present at `1f6d6b8` contained 1339. The **63** present
before archive retirement contained **1582** (746 theorems, 245 lemmas, 338 propositions, 253 corollaries).
Their full statements and nonstandard claim environments still require
reconciliation. In particular, the physics report distinguishes exact
identities `[E]`, conditional mathematical theorems `[C]`, assessments `[A]`
and imported results `[I]`; this inventory does not turn an assessment or a
finite symbolic check into a Lean theorem.

**Retracted source claim:** the revised
[analytic-geometry ring comparison](surcomplex/analytic-geometry/article.tex)
withdraws the earlier Noetherian/maximal-ideal/regular-completion package for
the fixed-polydisk ring `O(D)((t^Γ))`. It claims that package only for the
three other named rings. The finite-deformations report supplies division,
finite freeness, multiplicity conservation and residue duality under its own
hypotheses, without a Noetherian assumption. Its positive coefficient ideal
is not finitely generated for nonzero divisible `Γ`; this observation concerns
the integral coefficient ring and does not say that the Hahn field itself is
non-Noetherian. The correction changes no standard-environment count.

### September 22 inventory expansion

Commits `de84d8b`, `b147a9d` and `e9a9650`, followed by further report
merges, added ten reports and expanded six earlier ones. The canonical table
and statement index now count their current text. Historical package counts
must not be added to these totals: later merges consolidate repeated
statements and sometimes change their hypotheses. Every new obligation is
**pending unless mapped** in the implementation table.

### Corrections found while formalizing the placed reports

Each item below was reported by a formalization survey and then confirmed
independently by two reviewers, each of whom read the statement, its
standing conventions and its proof and tried to refute the claim. The source
corrections below have now been made and checked against the local proofs.
This records corrected prose and hypotheses, not new Lean coverage.

- **Corrected in source** (`prony:sec:sharp` and the literature comparison in the
  [Prony report](surcomplex/prony-reconstruction-at-surreal-scales/article.tex)):
  the unit-weight single-cluster formulas now require `n ≥ 2`.
  For `n = 1` the empty-sum and empty-maximum conventions give
  `d₁ = δ₁ = 0` and `Θ = v(w₁)`, hence `Θ = 0` for a valuation-zero weight.
- **Corrected in source** (`tate:thm:coordinates` and the corresponding clauses
  in `tate:thm:main` and `tate:node:thm:main`, in
  [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/article.tex)):
  the coordinate-family domain clause now requires `u ∈ K^×` (or `𝕂^×`
  in the general coefficient field). At `u = 0` both bilateral coordinate
  families are identically zero and strongly summable although `0 ∉ U_q`.
  The report now explains this exception; the README and catalogue agree.
- **Corrected in source** (discussion of `tate:eq:circlelayers` in
  [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/article.tex)):
  the rank-one circle quotient is `(H_α/H_α^-)/ℤᾱ`. The full quotient
  `H_α/ℤα` retains kernel `H_α^-`, even when the rank-one value group is
  `ℝ`. The example `Γ = ℝ ⊕lex ℝ`, `α = (1,0)` makes that kernel explicit.
  The introductory description now also distinguishes the kernels of
  `v mod H_α^-` on `K_{H_α}` and `v mod H_α` on `K_Γ`.
- **Corrected in source** (`tate:theta:eq:zerorow` in
  [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/article.tex)):
  the zero-row equation now uses `ξ₀`, the coarse reduction of the full
  solution `ξ`. Substituting `ξ₀` into the full coupled theta sum leaves
  leading term `−2 τ₁² τ₂⁻³` from lattice index `(−1,1)`, so the higher
  rows cannot be discarded. The displayed finite expansion of `ξ` remains
  valid, since the difference has positive first-coordinate valuation.
- **Clarified in source** (`diff:aut:lem:evaluation` and
  `diff:aut:lem:projective`, in
  [differential equations](surcomplex/differential-equations/article.tex)):
  formal maps used as inverse maps on infinitesimal tuples explicitly
  have zero constant term. The projective properness comparison is
  applied over the set-sized field generated by finitely many coordinates,
  with its induced valuation ring, rather than over a proper-class field.
  The direct reduction and local uniqueness proofs remain elementary;
  no new Lean coverage is claimed.
- **Clarified in source** (`diff:rs:sub:procedure`, in
  [differential equations](surcomplex/differential-equations/article.tex)):
  the finite regular-singular procedure requires effective coefficient
  operations as well as finite rational support. Complex algebraic
  entries give a concrete sufficient input class; arbitrary named complex
  constants do not by themselves provide exact spectral, equality and
  order operations. The finite-dependence theorem retains its full
  mathematical scope. The reduced weight set is now proved closed under
  all predecessor pairs, and the no-resonance case retains residual
  nilpotent blocks. No new Lean coverage is claimed.
- **Clarified in source** (`diff:rs:conv:alphabet`, in
  [differential equations](surcomplex/differential-equations/article.tex)):
  a gauge field is explicitly Euler-stable and contains `ℂ`. Translation
  by `∂ = −t∂_τ` always gives an identity in `No[i]`, but a system over
  a smaller Euler-stable field need not translate to a system over that
  field. For `E = K_(ℤ√2)`, the Euler equation `∂_τ y = y` has
  coefficient in `E`, whereas its intrinsic coefficient `−t` is outside
  `E`. The source now distinguishes this from the same-field equivalence
  when `t ∈ E`. No additional Lean coverage is claimed.
- **Corrected in source** (`diff:rs:lem:euler`, in
  [differential equations](surcomplex/differential-equations/article.tex)):
  `∂ = -t∂_T` preserves `K_Γ` exactly when `Γ = {0}` or `1 ∈ Γ`.
  The proof handles the constant field separately and derives `1 ∈ Γ`
  from the derivative of a nonconstant monomial in every nonzero group.
  The Euler derivative can delete the constant term, so its support is
  contained in the original support, rather than always equal to it.
- **Corrected in source** (`markov:prop:reversible`, in
  [Markov generators](surreal/markov-generators-at-every-scale/article.tex)):
  the converse now specifies a strictly coarsening chain from the discrete
  partition to the one-block partition, a strictly positive probability
  vector `π₀`, and strictly increasing scales. The proof gives the weighted
  matrices, verifies their endpoints and strict rank drops, and handles
  the one-state case. Without the final endpoint, the chain
  `{{1},{2},{3}} > {{1,2},{3}}` would end in rank `2`, contrary to an
  irreducible generator's rank-one final plateau.
- **Corrected in source** (`ihs:hh:prop:inner`, `ihs:sec:sharednot` and
  `ihs:rf:rem:nodiv`, in
  [infinite-dimensional spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex)):
  the claim that divisibility is necessary to define the Part I norm has
  been removed. For `δ = v(x)`, the proof factors
  `⟨x,x⟩ = ‖x_δ‖² t^{2δ}(1+u)` and constructs its positive root
  `‖x_δ‖ t^δ (1+u)^{1/2}` by the near-one binomial series.
  This proposition and the scalar modulus work for every ordered value
  group. For `Γ = ℤ` and an ordinary unit vector `e`, `‖te‖ = t`,
  even though the positive scalar `t` has no square root. A subsequent
  review of the Part I proofs removes their unused standing divisibility
  restriction. The closed-range theorem `ihs:hh:thm:closedrange` now holds
  at every rank: its range is the kernel of the continuous defect projection,
  whose nonnegative support gives `v(Πx) ≥ v(x)`. Only the real-valued
  metric-completeness subsection assumes `Γ ⊆ ℝ`. These strengthened
  source statements are not new Lean coverage.


The subsequent Part II source review also corrects the comparison of its
coherent diagonal algebra with `K^I`: equality holds for finite `I` or
trivial `Γ`, and strict inclusion requires infinite `I` and nonzero `Γ`.
Its projection calculus is vectorwise Hahn-additive; lack of an
operator-valued Hahn sum does not rule out a classical spectral measure.
The revised `ihs:rf:rem:notopsum` gives the relevant counterexample instead:
over `Γ = ℚ`, coordinate partial sums of
`Σₙ t^{1−1/(n+1)} eₙ` fail to converge in valuation. These corrections
add no Lean coverage.

A sixth confirmed report, that `tail:lem:signs` needs `char M ≠ 2` (in
characteristic `2`, `√(a+1) = √a + 1` over `𝔽₂(a)`), was already corrected in the
source by `506cd11`.

Two further reports were refuted by both reviewers and need no correction:
`meas:lem:prony`, where "a monic polynomial with distinct roots, all in `Ω`"
carries the standard meaning that it splits with simple roots in `Ω`; and the
field-generality remark in `hol:sec:fields`, since the generic point of the
several-variable proof can be taken in the uncountable field
`K = k((t^Γ))` itself (`Γ ≠ 0` by `hol:conv:group`).

## Main-report statement index

Every entry below is pending unless explicitly mapped to a checked declaration
in a later status update. Titles are copied from the LaTeX optional heading;
`Untitled` means the environment has no such heading. Labels are the exact
source labels, not Lean identifiers. An unlabeled statement is identified by
its source line. Line numbers are navigation hints for the current text; source
labels are the stable identifiers. This index does not include all mathematical
claims outside the four selected environments.

### computer-algebra

Source: [foundations-and-computation/computer-algebra/article.tex](foundations-and-computation/computer-algebra/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `cas:prop-countable` (line 564) | The finite-description bound |
| Theorem | `cas:thm-zerotest` (line 614) | Total coefficient access does not decide zero |
| Corollary | `cas:cor-sign` (line 666) | No universal three-way sign; equality reduces to zero testing |
| Corollary | `cas:cor-leading` (line 673) | No universal leading-term algorithm |
| Proposition | `cas:prop-validation` (line 699) | Unrestricted support validation is undecidable |
| Proposition | `cas:prop-leading` (line 719) | A high-rank leading-term and sign obstruction |
| Theorem | `cas:thm-core` (line 1079) | Effective rational monomial core |
| Theorem | `cas:thm-realclosure` (line 1209) | An implementable real-closed and algebraically closed layer |
| Theorem | `cas:thm-grid` (line 1439) | Finite extraction from a positive grid |
| Proposition | `cas:prop-precision` (line 1590) | Basic certified precision rules |
| Proposition | `cas:prop-finiteprefix` (line 1636) | Finite-prefix criterion for rank-one grids |
| Proposition | `cas:prop-lift` (line 2154) | Correctness of infinitesimal substitution |
| Proposition | `cas:prop-periods` (line 3399) | Every global extension acquires an infinite period |
| Proposition | `cas:prop-archimedean` (line 3756) | No order-preserving embedding |

### foundations

Source: [foundations-and-computation/foundations/article.tex](foundations-and-computation/foundations/article.tex).

The revised `found:prop:positive` retains a positive, well-ordered control
set; ordinary formal-series evaluation does not by itself prove this nonlinear
recursion theorem. The new `found:ex:boundedrankone` remains **pending**,
including the obstruction for the net of all finite subsums. The prose after
`found:prop:twotopologies` adds equality of intrinsic order-modulus and valuation
topologies and the geometric convergence criterion that the multiples of the
positive exponent be cofinal. These intrinsic-topology claims remain **pending**
and are separate from the proved actual fine-topology nonconvergence.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `found:prop:proper` (line 673) | There is no set of all surreal numbers |
| Proposition | `found:prop:allcuts` (line 726) | The unrestricted cut axiom is inconsistent |
| Lemma | `found:lem:bounds` (line 757) | Bounds for sets of surreals; the small positive lower bound |
| Proposition | `found:prop:incomplete` (line 802) | Untitled |
| Proposition | `found:prop:scott` (line 943) | Set codes for a definable class quotient |
| Proposition | `found:prop:recursion` (line 1233) | Local recursion and coherent assembly |
| Proposition | `found:prop:universe` (line 1356) | Why universe relativization avoids the cut contradiction |
| Proposition | `found:prop:universecut` (line 1375) | The missing self-cut |
| Proposition | `found:prop:closure` (line 1479) | Closure under a fixed set of finitary operations |
| Proposition | `found:prop:complex` (line 1573) | Finite data complexify safely |
| Theorem | `found:thm:workspace` (line 1721) | Workspace localization |
| Theorem | `found:thm:finitepoints` (line 1909) | Finite algebra over an algebraically closed base |
| Proposition | `found:prop:positive` (line 2075) | Support-local nonlinear recursion |
| Corollary | `found:cor:fixeddomain` (line 2118) | Fixed domain |
| Proposition | `found:ex:rescaling` (line 2258) | Universal rescaling fails in a fixed Hahn field |
| Proposition | `found:prop:rescalingpositive` (line 2286) | The enlarged group repairs it |
| Theorem | `found:thm:discrete` (line 2485) | Small subsets and small-index nets are discrete |
| Proposition | `found:prop:twotopologies` (line 2547) | Intrinsic and full-class subspace topologies differ |
| Lemma | `found:lem:nometric` (line 2616) | No countable ball basis is coinitial |
| Corollary | `found:cor:nopaths` (line 2674) | No nonconstant fine-continuous paths |
| Proposition | `found:prop:period` (line 2921) | Why an infinite period is not a paradox |
| Proposition | `found:prop:signtree` (line 3045) | Sign-tree categoricity |
| Proposition | `found:prop:univalence` (line 3464) | The elementary incompatibility test |

### surreal-scalars-and-spacetime

Source: [physics/surreal-scalars-and-spacetime/article.tex](physics/surreal-scalars-and-spacetime/article.tex).

The maintained report expands `phys:prop:pole`: substituting `r = s^q w(s)`
gives leading Laurent coefficient `c w(0)^(-p)` and pole order `pq`. Its
Schwarzschild summaries now include the factor `w(0)^(-6)` and the nonzero-mass
hypothesis. Normalized finite tests do not prove coefficient invariance for
arbitrary units; the formal-series statement remains pending.

All statements in this newly indexed report remain **pending**. The
`\TC` heading marker denotes a conditional mathematical claim; its stated
hypotheses must be retained. Exact computations, assessments and imported
physical results outside the four standard environments are separate claims.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `phys:prop:st` (line 848) | \TC\ Standard part |
| Proposition | `phys:prop:elementary` (line 873) | \TC\ Two elementary obstructions |
| Proposition | `phys:prop:discrete` (line 957) | \TC\ Set-sized collapse in the full fine topology |
| Proposition | `phys:prop:frame` (line 1166) | \TC\ Bounded-frame valuation invariance |
| Lemma | `phys:lem:balance` (line 1188) | \TC\ Dominant balance: the minimum is attained twice |
| Proposition | `phys:prop:pole` (line 1466) | \TC\ Route 1, valuation-theoretic: poles survive scalar extension and ramification |
| Proposition | `phys:prop:unlimited` (line 1503) | \TC\ Route 2, order-theoretic: a leading pole stays unlimited in every ordered extension |
| Corollary | `phys:cor:noext` (line 1555) | \TC\ The real-analytic geometric consequence |
| Proposition | `phys:prop:noendpoint` (line 1573) | \TC\ No field-valued Schwarzschild endpoint |
| Proposition | `phys:prop:crossover` (line 1930) | \TC\ The small-$J$ limit, uniform on bounded intervals |
| Theorem | `phys:thm:einstein` (line 2197) | {\TC\ Reduction of the Einstein tensor over $C^{\infty}(U,\R)[[h]]$} |
| Theorem | `phys:thm:reduction` (line 2254) | \TC\ Standard-part reduction over a Hahn coefficient algebra |
| Corollary | `phys:cor:shadow` (line 2296) | \TC\ Positive-order corrections cannot repair a singular shadow |
| Proposition | `phys:prop:matching` (line 2632) | \TC\ Outer and inner strong-summability criteria |
| Theorem | `phys:thm:spectral` (line 2720) | \TC\ Finite Hermitian spectral theorem |
| Theorem | `phys:thm:quantumshadow` (line 2759) | \TC\ Reduction of finite quantum protocols |
| Proposition | `phys:prop:phase` (line 3002) | \TC\ Canonical phase versus scalar differentiation |
| Corollary | `phys:cor:constantphase` (line 3020) | \TC\ The canonical global phase is constant in ordinary time |
| Proposition | `phys:prop:periods` (line 3040) | \TC\ Infinite periods of a global phase homomorphism |

### analysis

Source: [surcomplex/analysis/article.tex](surcomplex/analysis/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `a:prop:triangle` (line 188) | Modulus identities over an ordered field |
| Lemma | `a:lem:valbound` (line 293) | Crude valuation bound |
| Proposition | `a:prop:fragment` (line 362) | Containment of set-sized data |
| Lemma | `a:lem:neumann` (line 693) | Neumann support lemma |
| Corollary | `a:cor:complexsub` (line 738) | No growth condition |
| Theorem | `a:thm:discrete` (line 847) | Set-sized convergence collapses, with a uniform radius |
| Proposition | `a:prop:clopen` (line 891) | Clopen infinitesimal cosets |
| Corollary | `a:cor:nopath` (line 910) | No nonconstant continuous paths |
| Proposition | `b:inclusions` (line 1069) | The inclusions, and what witnesses them |
| Proposition | `b:fivefailures` (line 1145) | Five classical statements fail in the germ-analytic class |
| Proposition | `b:noremoval` (line 1220) | No unrestricted removability theorem |
| Proposition | `b:twistwitness` (line 1249) | The twisted-exponential witness |
| Theorem | `b:nogo` (line 1295) | Contour no-go |
| Corollary | `b:nogo-fundamental` (line 1325) | The fundamental theorem cannot be widened |
| Corollary | `b:log-not-coherent` (line 1334) | $\mathcal L$ is not a coherent primitive of $1/z$ |
| Corollary | `b:primitive-uniqueness-scope` (line 1347) | Uniqueness of primitives is a coherent statement |
| Lemma | `b:blocks` (line 1417) | Separated degree blocks |
| Theorem | `b:realization` (line 1487) | Realization of every formal series |
| Proposition | `b:remainder` (line 1546) | Uniform Taylor remainder |
| Corollary | `b:nogrowth` (line 1587) | No growth condition |
| Proposition | `b:globalseries` (line 1604) | Everywhere-summable means polynomial |
| Theorem | `b:germalgebra` (line 1636) | {The germ algebra is $\K[[X]]$} |
| Corollary | `b:isolated` (line 1700) | Isolated zeros of a germ |
| Theorem | `b:derivation-obstruction` (line 1744) | Derivation obstruction |
| Theorem | `b:CRgerm` (line 1795) | Cauchy--Riemann criterion for germs |
| Theorem | `b:harmonicgerm` (line 1830) | Harmonic conjugate germs |
| Theorem | `b:inverse` (line 1869) | Local inverse and implicit function theorems for germs |
| Theorem | `b:ramification` (line 1907) | Finite ramification normal form |
| Corollary | `b:localopen` (line 1937) | Local openness and no local modulus maximum |
| Corollary | `b:localidentity` (line 1979) | Local identity and maximum-modulus principles |
| Proposition | `b:formalprimitive` (line 2032) | The only local primitive obstruction |
| Theorem | `b:reschange` (line 2049) | Change of variable, with the ramification factor |
| Corollary | `b:localargument` (line 2071) | Local argument principle |
| Proposition | `b:formalres` (line 2080) | Formal residue facts and removability |
| Theorem | `b:lagrange` (line 2115) | Lagrange--B\"urmann inversion |
| Theorem | `c:p4:eval` (line 2330) | Faithful coherent evaluation |
| Corollary | `c:p4:shadow` (line 2386) | Leading coefficients control zero shadows |
| Theorem | `c:p4:monadtaylor` (line 2397) | Exact monad-wide Taylor expansion |
| Theorem | `c:p4:derivbridge` (line 2426) | The section derivative is the fine derivative |
| Proposition | `c:p4:prop-units` (line 2476) | Units |
| Proposition | `c:p4:prop-calculus` (line 2498) | Infinitesimal functional calculus |
| Theorem | `c:p4:composition` (line 2525) | Admissible composition |
| Proposition | `c:p4:chartchange` (line 2569) | Chart-change criterion |
| Theorem | `c:p4:identity` (line 2616) | Identity theorem for coherent sections |
| Theorem | `c:p4:gluing` (line 2676) | Gluing over the ordinary base |
| Theorem | `c:p4:lift` (line 2724) | Functoriality of the lift |
| Proposition | `c:p4:liftzeros` (line 2754) | A lift creates no displaced zeros |
| Theorem | `c:p4:bridge` (line 2801) | Scale embedding of arbitrary formal series |
| Proposition | `c:p4:obstruction` (line 2836) | An obstruction in the original chart |
| Proposition | `c:p5:calculus` (line 2914) | Elementary calculus of the functional |
| Lemma | `c:p5:positivity` (line 2972) | Positivity of the coefficientwise integral |
| Theorem | `c:p5:ML` (line 2997) | Surcomplex ML inequality |
| Theorem | `c:p5:cauchy` (line 3062) | Cauchy's theorem and integral formula |
| Corollary | `c:p5:cauchyest` (line 3116) | Cauchy estimates from a pointwise surreal bound |
| Corollary | `c:p5:scaledCauchy` (line 3140) | Cauchy estimates in an affine chart |
| Lemma | `c:p5:csmajorant` (line 3172) | Cauchy--Schwarz majorant lemma |
| Proposition | `c:p5:majorant` (line 3188) | Coefficientwise Cauchy estimate |
| Theorem | `c:p5:morera` (line 3238) | Coefficientwise Morera |
| Theorem | `c:p5:primitive` (line 3275) | Coherent primitives |
| Lemma | `d:lem:ordinarydivision` (line 3432) | Ordinary division, extended coefficientwise |
| Theorem | `d:thm:preparation` (line 3473) | Hahn--Weierstrass preparation, global form |
| Corollary | `d:cor:localprep` (line 3598) | Local preparation at a single zero |
| Theorem | `d:thm:division` (line 3636) | Hahn--Weierstrass division |
| Lemma | `d:lem:smallroots` (line 3674) | Finite roots and infinitesimal corrections |
| Theorem | `d:thm:zerocluster` (line 3703) | Exact zero clustering; specialization of the zero divisor |
| Corollary | `d:cor:displacement` (line 3778) | Simple-root lifting and its displacement |
| Theorem | `d:thm:rouchevaluation` (line 3827) | Valuation Rouch\'e: fibrewise stability |
| Theorem | `d:thm:rouchemargin` (line 3844) | Ordinary-margin Rouch\'e: stability of the total |
| Corollary | `d:cor:rouchereal` (line 3876) | Real-margin Rouch\'e: a surcomplex-valued hypothesis |
| Theorem | `d:thm:moments` (line 3945) | Contour moments of a zero cluster |
| Theorem | `d:thm:Hresidue` (line 4137) | Cluster residue theorem on $\Mc(U)$ |
| Proposition | `d:prop:quotientinM` (line 4196) | Quotients of coherent families lie in $\Mc(U)$ |
| Theorem | `d:thm:bridge1` (line 4226) | Residue-cluster theorem |
| Theorem | `d:thm:residuequotient` (line 4298) | Residue theorem for coherent quotients, global form |
| Theorem | `d:thm:bridge2` (line 4337) | Uniformly bounded pole order |
| Theorem | `d:thm:weightedarg` (line 4417) | Exact weighted argument principle |
| Corollary | `d:cor:zerosminuspoles` (line 4477) | Zeros minus poles |
| Theorem | `d:thm:deformation` (line 4511) | Deformation invariance under admissible infinitesimal deformations |
| Theorem | `d:thm:rationalresidue` (line 4567) | Global rational residue theorem |
| Lemma | `e:lem-normalize` (line 4666) | Infinitesimal rescaling; monomial radius |
| Theorem | `e:thm-openmapping` (line 4723) | Local finite degree and the open mapping theorem |
| Corollary | `e:cor-maxmod` (line 4752) | Strong local maximum modulus |
| Lemma | `e:lem-reversion` (line 4791) | Hahn reversion |
| Theorem | `e:thm-localinverse` (line 4824) | Coherent local inverse |
| Proposition | `e:prop-autobounded` (line 4858) | Automatic surreal boundedness |
| Theorem | `e:thm-realliouville` (line 4890) | Real-bounded macroscopically entire functions |
| Theorem | `e:thm-coeffliouville` (line 4933) | Coefficientwise growth and polynomial degree |
| Theorem | `e:thm-removable` (line 4996) | Coefficientwise removal is necessary and sufficient |
| Theorem | `e:thm-schwarzpick` (line 5051) | Schwarz--Pick for canonical lifts |
| Corollary | `e:cor-schwarz` (line 5099) | Schwarz lemma for canonical lifts |
| Corollary | `e:cor-spstability` (line 5114) | Stability away from the equality case |
| Theorem | `e:thm-biholo` (line 5161) | Lifting of infinitesimally deformed biholomorphisms |
| Corollary | `e:cor-liftbiholo` (line 5198) | Lifted conformal equivalence |
| Corollary | `e:cor-riemannmap` (line 5204) | Standard-halo Riemann mapping theorem |
| Theorem | `e:thm-montel` (line 5239) | Countable-support Montel theorem |
| Theorem | `e:thm-harmonic` (line 5301) | Coefficientwise harmonic conjugates |
| Theorem | `e:thm-poisson` (line 5327) | Poisson's formula and a coherent Dirichlet problem |
| Theorem | `e:thm-reflection` (line 5370) | Coherent Schwarz reflection |
| Proposition | `e:prop-infexp` (line 5422) | Infinitesimal exponential and logarithm |
| Proposition | `e:prop-polar` (line 5455) | The finite exponential and the polar form |
| Theorem | `e:thm-exp` (line 5518) | Properties of the canonical exponential |
| Theorem | `e:thm-twisted` (line 5606) | The twisted global exponentials |
| Corollary | `e:cor-twistwitness` (line 5662) | A structured unit-modulus witness |
| Theorem | `e:thm-periodobstruction` (line 5684) | The period obstruction |
| Theorem | `e:thm-globallog` (line 5738) | A logarithm on the whole punctured class plane |
| Corollary | `e:cor-lognotcoherent` (line 5782) | $\mathcal L$ is not a coherent primitive of $1/z$ |
| Theorem | `e:thm-principallog` (line 5831) | Principal logarithm on the cut plane |
| Proposition | `e:prop-logdiscrepancy` (line 5857) | $\mathcal L$ and $\Log$ are different functions |
| Theorem | `e:thm-logcharts` (line 5903) | Logarithm charts on multiplicative monads |
| Theorem | `e:thm-picard` (line 5941) | Every nonzero value at every surreal scale |
| Theorem | `f:thm-affine` (line 6070) | Affine transport of the coherent theory |
| Proposition | `f:prop-chartchange` (line 6163) | Chart-change criterion |
| Corollary | `f:cor-scaledCauchy` (line 6220) | Cauchy estimates at an arbitrary coherent scale |
| Theorem | `f:thm-rigidity` (line 6292) | All-scale polynomial rigidity |
| Corollary | `f:cor-globalclassical` (line 6355) | Global classical consequences in the rigid category |
| Lemma | `f:lem-polefree` (line 6417) | A pole-free coherent fraction is coherent holomorphic |
| Theorem | `f:thm-rationalrigidity` (line 6471) | All-scale rational rigidity |

### analytic-geometry

Source: [surcomplex/analytic-geometry/article.tex](surcomplex/analytic-geometry/article.tex).

The corrected `analytic:conv:notation` defines the standard-part pullback
topology on finite tuples and identifies its restriction to the zero monad
as indiscrete. These induced-topology claims remain **pending**; the mapped
`StandardPartTopology` results prove continuity and clopen fibers in the fine
topology instead.

The fixed-polydisk package previously attributed in the prose is retracted;
see the canonical inventory note above. The 86 standard environments below
retain their own ring hypotheses.

The expansion adds 33 pending obligations about common-domain holomorphic
Hahn coefficients, corona obstructions, spectral fibres and local rings.
They require ordinary holomorphic interpolation and the stated common-domain
support conditions; generic Hahn-field algebra alone does not establish them.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `analytic:thm:overview-structure-A` (line 326) | Structure of the radius-free ring $\A_n$, overview |
| Theorem | `analytic:thm:overview-structure-R` (line 339) | Structure and finite maps for the common-domain ring $\RR_n$, overview |
| Theorem | `analytic:thm:overview-deform` (line 351) | Conservation, duality and the radius-free strengthening, overview |
| Theorem | `analytic:thm:overview-stability` (line 372) | Quantitative stability over $\A_n$, overview |
| Theorem | `analytic:thm:overview-fixed` (line 381) | The fixed-polydisk ring $\OO(D)((t^\Gamma))$, overview |
| Lemma | `analytic:lem:enlargement` (line 536) | Enlargement rule |
| Lemma | `analytic:lem:neumann` (line 569) | Hahn--Neumann support lemma |
| Lemma | `analytic:lem:operator` (line 598) | Positive-support operator inversion |
| Proposition | `analytic:prop:units` (line 693) | Units of $\A_n$ |
| Proposition | `analytic:prop:translation` (line 706) | Evaluation and translation over $\A_n$ |
| Proposition | `analytic:prop:kernels` (line 739) | Evaluation kernels and finite jets over $\A_n$ |
| Proposition | `analytic:prop:faithful` (line 760) | Faithful interpretation as functions on the monad |
| Proposition | `analytic:prop:evaluationR` (line 820) | Evaluation, support and translation over $\RR_n$ |
| Lemma | `analytic:lem:density` (line 857) | Infinitesimal evaluation detects nonzero elements of $\RR_n$ |
| Theorem | `analytic:thm:divisionA` (line 954) | Hahn-germ division over $\A_n$ |
| Theorem | `analytic:thm:prepA` (line 983) | Preparation and finite projection over $\A_n$ |
| Corollary | `analytic:cor:hypersurface-fiber` (line 1020) | Fibres of a prepared hypersurface over $\A_n$ |
| Theorem | `analytic:thm:prepR` (line 1068) | Parameterized Hahn preparation over $\RR_n$ |
| Theorem | `analytic:thm:divisionR` (line 1108) | Parameterized Hahn division over $\RR_n$ |
| Corollary | `analytic:cor:freehypersurfaceR` (line 1134) | Finite free hypersurface quotient over $\RR_n$ |
| Theorem | `analytic:thm:noetherianA` (line 1172) | Noetherianity of $\A_n$ |
| Theorem | `analytic:thm:weak-nullA` (line 1187) | Weak Nullstellensatz over $\A_n$ |
| Theorem | `analytic:thm:strong-nullA` (line 1217) | Jacobson property and strong Nullstellensatz over $\A_n$ |
| Theorem | `analytic:thm:regularA` (line 1249) | Local geometry of $\A_n$ |
| Theorem | `analytic:thm:noetherianR` (line 1299) | Noetherian monad ring $\RR_n$ |
| Proposition | `analytic:prop:normalization` (line 1328) | Noether normalization over $\RR_n$ |
| Theorem | `analytic:thm:weaknullR` (line 1352) | Weak monad Nullstellensatz over $\RR_n$ |
| Theorem | `analytic:thm:strongnullR` (line 1378) | Strong monad Nullstellensatz over $\RR_n$ |
| Proposition | `analytic:prop:completionR` (line 1421) | Local coordinates and completion over $\RR_n$ |
| Theorem | `analytic:thm:finitemap` (line 1467) | Finite projection and generic fibres over $\RR_n$ |
| Lemma | `analytic:lem:residue-annihilate` (line 1675) | Well-definedness and annihilation over $\A_n$ |
| Lemma | `analytic:lem:spanning` (line 1711) | Spanning with a support certificate, over $\A_n$ |
| Theorem | `analytic:thm:finite-deformA` (line 1732) | Finite complete-intersection deformation over $\A_n$: the radius-free strengthening |
| Theorem | `analytic:thm:conjugacy` (line 1824) | Positive Hahn conjugacy |
| Lemma | `analytic:lem:ordinarykoszul` (line 1867) | Ordinary contraction on one fixed neighbourhood |
| Theorem | `analytic:thm:conservationR` (line 1910) | Support-explicit conservation of multiplicity over $\RR_n$ |
| Corollary | `analytic:cor:matrices` (line 1990) | Infinitesimal coordinate eigenvalues |
| Theorem | `analytic:thm:residueduality` (line 2046) | Support-controlled residue duality over $\RR_n$ |
| Proposition | `analytic:prop:residues-agree` (line 2095) | The two residue functionals agree where both are defined |
| Corollary | `analytic:cor:residueframe` (line 2118) | A support-controlled constant residue frame |
| Lemma | `analytic:lem:finite-dependency` (line 2155) | Finite dependency at a prescribed exponent |
| Theorem | `analytic:thm:trace` (line 2176) | Trace--Jacobian identity |
| Theorem | `analytic:thm:zeros` (line 2228) | Conservation of singular zeros |
| Proposition | `analytic:prop:jacobian` (line 2275) | Four equivalent forms of the simple-root criterion |
| Corollary | `analytic:cor:weighted` (line 2290) | Weighted evaluation and simple residues |
| Theorem | `analytic:thm:workspace` (line 2343) | Workspace invariance over $\A_n$ |
| Theorem | `analytic:thm:basechange` (line 2373) | Base change and full surcomplex exhaustiveness over $\RR_n$ |
| Corollary | `analytic:cor:full-sc` (line 2405) | Full-surcomplex conservation |
| Theorem | `analytic:thm:formal-comparison` (line 2458) | Analytic--formal comparison |
| Lemma | `analytic:lem:scaled-polynomial` (line 2540) | Scaled Taylor polynomials at each Hahn exponent |
| Theorem | `analytic:thm:local-stability` (line 2558) | One-root Hensel--Rouch\'e bound over $\A_n$ |
| Corollary | `analytic:cor:separation` (line 2615) | Separation of simple zeros |
| Theorem | `analytic:thm:cluster-stability` (line 2632) | Finite-cluster correspondence |
| Corollary | `analytic:cor:nonpolynomial` (line 3070) | A nonpolynomial length-five cluster over $\RR_2$ |
| Lemma | `analytic:lem:fixed-eval` (line 3185) | Evaluation estimate over $\HH_\Gamma(D)$ |
| Lemma | `analytic:lem:fixed-global-unit` (line 3208) | A sufficient global unit criterion |
| Proposition | `analytic:prop:fixed-banach` (line 3241) | Completeness and exact pointwise norm |
| Lemma | `analytic:lem:fixed-distance` (line 3286) | Unit neighbourhood and a distance obstruction |
| Lemma | `analytic:lem:fixed-cardinal` (line 3323) | The cardinal functions |
| Lemma | `analytic:lem:fixed-interp` (line 3338) | Unrestricted ordinary interpolation on $D$ |
| Theorem | `analytic:thm:fixed-quotient` (line 3379) | Fixed-divisor interpolation quotient |
| Proposition | `analytic:prop:fixed-Bnorm` (line 3418) | The quotient norm |
| Lemma | `analytic:lem:fixed-two-orders` (line 3442) | Two orders |
| Theorem | `analytic:thm:fixed-units` (line 3453) | Exact unit criterion in the common-support product |
| Corollary | `analytic:cor:fixed-inverseclosed` (line 3496) | Failure of inverse-closedness |
| Corollary | `analytic:cor:fixed-matrix` (line 3510) | Matrix inverse criterion |
| Theorem | `analytic:thm:fixed-bezout` (line 3531) | Exact B\'ezout criterion modulo a fixed simple divisor |
| Theorem | `analytic:thm:fixed-corona` (line 3589) | Uniform corona failure over $\HH(D)$ |
| Lemma | `analytic:lem:fixed-hzeros` (line 3639) | Simple ordinary zeros acquire no extra monad zeros |
| Proposition | `analytic:prop:fixed-sharp-corona` (line 3662) | The sharp uniform lower bound |
| Proposition | `analytic:prop:fixed-local-bezout` (line 3697) | Local B\'ezout solutions on ordinary neighbourhoods |
| Proposition | `analytic:prop:fixed-nonprincipal` (line 3712) | A proper, nonprincipal, two-generated free ideal |
| Lemma | `analytic:lem:fixed-division` (line 3807) | Support-controlled divided difference over $\HH_\Gamma(D)$ |
| Corollary | `analytic:cor:fixed-eval-ideal` (line 3837) | Geometric evaluation ideals |
| Lemma | `analytic:lem:fixed-finite-order` (line 3851) | Finite order of vanishing |
| Theorem | `analytic:thm:fixed-dvr` (line 3864) | Geometric discrete valuation rings over $\HH_\Gamma(D)$ |
| Corollary | `analytic:cor:fixed-completion` (line 3896) | Finite jets and completion |
| Theorem | `analytic:thm:fixed-gauge-prime` (line 3960) | Prime ideals from arbitrary positive gauges |
| Proposition | `analytic:prop:fixed-contraction` (line 4024) | All the gauges contract to one classical maximal ideal |
| Theorem | `analytic:thm:fixed-two-ideals` (line 4054) | Two ideals over the same classical point |
| Theorem | `analytic:thm:fixed-fibre` (line 4104) | Infinite relative dimension, and failure of Noetherianity |
| Corollary | `analytic:cor:fixed-basechange` (line 4136) | Coefficientwise reduction is not scalar base change |
| Theorem | `analytic:thm:fixed-closure` (line 4160) | Closure collapse of the prime chain |
| Proposition | `analytic:prop:fixed-invisible` (line 4208) | Nongeometric maximal ideals |
| Corollary | `analytic:cor:fixed-real` (line 4239) | Real coefficient form |
| Theorem | `analytic:thm:fixed-structure` (line 4301) | Structure of the fixed-polydisk ring |

### contours-and-stokes

Source: [surcomplex/contours-and-stokes/article.tex](surcomplex/contours-and-stokes/article.tex).

The expansion adds 19 standard environments for untransformed Leray cycles.
Those obligations remain **pending** and retain a convergent isolated leading
map, a positive lower bound on perturbation support and the specified ordinary
covering-cycle category. They do not remove the determinant factors from the
earlier transformed coordinate-torus formulas or assert fine-continuous cycles.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `contours:lem:support` (line 431) | Support mechanism |
| Proposition | `contours:prop:fullfine` (line 630) | Full-class discreteness of sets |
| Proposition | `contours:prop:intrinsic` (line 661) | Intrinsic total separation |
| Proposition | `contours:prop:noftc` (line 711) | No endpoint integration for all fine-local primitives |
| Proposition | `contours:prop:mesh` (line 749) | Finite-partition obstruction |
| Theorem | `contours:thm:stdpartjordan` (line 807) | Jordan separation in the standard-part topology |
| Theorem | `contours:thm:sajordan` (line 881) | Semialgebraic Jordan theorem; classical input |
| Theorem | `contours:thm:polstokes` (line 1024) | Polynomial-chain Stokes |
| Theorem | `contours:thm:hahnstokes` (line 1117) | Hahn-valued generalized Stokes |
| Proposition | `contours:prop:poincare` (line 1166) | Support-preserving Poincar\'e lemma |
| Theorem | `contours:thm:cohomology` (line 1188) | Cohomology of the globally supported Hahn complex |
| Lemma | `contours:lem:pullback` (line 1335) | Pullback and differential with a support certificate |
| Theorem | `contours:thm:deformedstokes` (line 1399) | Stokes for Hahn-deformed chains |
| Theorem | `contours:thm:homotopy` (line 1496) | Hahn homotopy formula |
| Proposition | `contours:prop:ml` (line 1543) | An order-valued parameter estimate |
| Theorem | `contours:thm:cauchy` (line 1604) | Coherent Cauchy theorem |
| Theorem | `contours:thm:endpoints` (line 1642) | Exact endpoint-transport formula |
| Theorem | `contours:thm:winding` (line 1719) | Winding stability at one scale |
| Theorem | `contours:thm:cauchyformula` (line 1752) | Cauchy formula at displaced points and on deformed contours |
| Corollary | `contours:cor:deformedres` (line 1822) | Residues on a deformed protecting contour |
| Proposition | `contours:prop:overlap` (line 1897) | Agreement on admissible overlaps |
| Theorem | `contours:thm:rescaling` (line 1988) | Positive rescaling gives polynomial coefficient families |
| Theorem | `contours:thm:localcauchy` (line 2055) | Cauchy formula for a radius-free germ |
| Lemma | `contours:lem:protect` (line 2088) | A radius protecting an entire one-variable cluster |
| Theorem | `contours:thm:microcircle` (line 2112) | Microscopic circle realization of the one-variable perturbation residue |
| Theorem | `contours:thm:localresidue` (line 2160) | Radius-free moving-pole residue theorem |
| Theorem | `contours:thm:microtorus` (line 2269) | Coordinate-power torus realization |
| Lemma | `contours:lem:residuetransform` (line 2357) | Transformation of the Hahn perturbation residue |
| Theorem | `contours:thm:generalrepresentation` (line 2395) | Microscopic contour representation of a general residue |
| Theorem | `contours:thm:septorus` (line 2545) | Separating-torus realization; conditional on \cite{Geometry} |
| Lemma | `contours:lem:radiusfreesub` (line 2883) | Radius-free substitution into a Hahn map |
| Corollary | `contours:cor:radialeval` (line 2921) | Radial evaluation of an ordinary family |
| Lemma | `contours:lem:positiveimplicit` (line 2958) | Positive implicit equation |
| Lemma | `contours:lem:targetmonomial` (line 3034) | A discriminant-avoiding monomial direction in the \emph{target} |
| Theorem | `contours:thm:ramifiedleray` (line 3072) | Ramified Leray family; ordinary analysis |
| Lemma | `contours:lem:constantperiod` (line 3140) | Coefficientwise constant-period identity |
| Proposition | `contours:prop:admissiblepullback` (line 3213) | Admissibility of the untransformed pullback |
| Theorem | `contours:thm:untransformed` (line 3260) | Universal untransformed contour |
| Corollary | `contours:cor:scalecancel` (line 3316) | Cancellation of the auxiliary scales |
| Lemma | `contours:lem:radialbounds` (line 3387) | Finite radial bounds |
| Theorem | `contours:thm:adaptedlift` (line 3457) | Equation-adapted lift on the same cover |
| Corollary | `contours:cor:protectedsheets` (line 3513) | Regular protected sheets |
| Lemma | `contours:lem:straighthomotopy` (line 3559) | Admissible straight homotopy |
| Theorem | `contours:thm:untransformedhomotopy` (line 3586) | Untransformed homotopy invariance |
| Theorem | `contours:thm:degreenormalization` (line 3631) | Degree normalization on the adapted cycle |
| Corollary | `contours:cor:protectedtrace` (line 3682) | Protected trace representation |
| Proposition | `contours:prop:idealannihilation` (line 3714) | Annihilation of the equation ideal, and descent |
| Lemma | `contours:lem:finitejet` (line 3757) | Finite-jet extension of an ordinary local residue |
| Theorem | `contours:thm:formalcontour` (line 3782) | Formal-coefficient contour theorem |
| Theorem | `contours:thm:algpairing` (line 4248) | Characterization and algebraic Cauchy theory |
| Proposition | `contours:prop:rationalcohomology` (line 4301) | Rational de Rham quotient |
| Proposition | `contours:prop:comparison` (line 4346) | Comparison on separated charts |
| Proposition | `contours:prop:samplingcriterion` (line 4466) | A precise sampling criterion |
| Theorem | `contours:thm:sampling` (line 4511) | Coefficientwise recovery of a Hahn contour |

### differential-equations

Source: [surcomplex/differential-equations/article.tex](surcomplex/differential-equations/article.tex).

All statements in this newly indexed report remain **pending**.

**Needs correction:** the prose warning `diff:warn:collapse` and the two
README summaries say that replacing `∂O` by `O` makes the criterion
"`b` infinitesimal." Since `O` is defined as the finite surreals, that
replacement instead makes the criterion "`b` finite." The displayed
infinitesimal counterexample refutes either weakened criterion. This
wording issue does not establish or refute the pending logarithmic-derivative
image theorem; the wording correction remains separate from that proof obligation.

The expansion adds 25 pending obligations for the Hermitian spectral–integral
package and its consequences. It requires the Berarducci–Mantova derivation,
finite-primitive phase quotient, differential existence/transfer results and
Hermitian matrix theory; formal Hahn scalar calculus is not a substitute.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `diff:lem:neumann` (line 613) | Positive-support calculus |
| Theorem | `diff:thm:BM` (line 655) | Berarducci--Mantova: imported input |
| Proposition | `diff:prop:algdiff` (line 763) | Algebraic implicit differentiation |
| Proposition | `diff:prop:complexification` (line 784) | Unique extension to $\SC$ |
| Proposition | `diff:prop:realexp` (line 833) | Real exponential integration |
| Lemma | `diff:lem:smallnegative` (line 857) | Order reversal on infinitesimals, and smallness |
| Proposition | `diff:prop:coarse` (line 914) | A preliminary obstruction |
| Proposition | `diff:prop:rescale` (line 1062) | Change of independent scale changes the solvability data |
| Proposition | `diff:prop:totalchain` (line 1083) | The two formal derivations commute; the valid polynomial chain rule |
| Proposition | `diff:prop:chain` (line 1118) | Two-derivative chain rule for series, with derived summability |
| Lemma | `diff:lem:smallchain` (line 1419) | Formal identities survive infinitesimal evaluation |
| Theorem | `diff:thm:unitphase` (line 1496) | Unique infinitesimal phase residue |
| Theorem | `diff:thm:cisgroup` (line 1544) | Finite-angle phase group, with its differential identity |
| Corollary | `diff:cor:polar` (line 1594) | Branch-free polar form |
| Proposition | `diff:prop:normprimitive` (line 1650) | Normalized primitive |
| Proposition | `diff:prop:RB` (line 1692) | Integration by parts, and a Rota--Baxter correction |
| Theorem | `diff:thm:idealstructure` (line 1756) | Structure of the bounded-primitive ideal |
| Theorem | `diff:thm:logimage` (line 1868) | Exact logarithmic-derivative image |
| Theorem | `diff:thm:phasecriterion` (line 1924) | Finite-primitive criterion for rank-one equations |
| Corollary | `diff:cor:oscillator` (line 2002) | The missing oscillator |
| Corollary | `diff:cor:rotation` (line 2066) | The unit-circle version |
| Corollary | `diff:cor:riccati` (line 2086) | A Riccati transfer |
| Theorem | `diff:thm:gauge` (line 2151) | Purely infinite phase normal form, with uniqueness |
| Corollary | `diff:cor:exact` (line 2195) | Obstruction exact sequence |
| Corollary | `diff:cor:tensor` (line 2226) | Tensor, dual, and no finite-order obstruction |
| Theorem | `diff:thm:power` (line 2273) | Sharp support threshold |
| Corollary | `diff:cor:power` (line 2316) | Power threshold |
| Corollary | `diff:cor:logscales` (line 2332) | Iterated-logarithm thresholds at every finite depth |
| Theorem | `diff:thm:rational` (line 2426) | Rational phase criterion |
| Theorem | `diff:thm:strip` (line 2547) | The strip exponential |
| Theorem | `diff:thm:maximalstrip` (line 2584) | Exact domain of the exponential differential equation |
| Theorem | `diff:thm:maximalstripalt` (line 2596) | Maximality restated |
| Corollary | `diff:cor:noglobalPsi` (line 2629) | Phase-independent nonexistence |
| Proposition | `diff:prop:defect` (line 2659) | Character-independent invariant defect |
| Theorem | `diff:thm:variation` (line 2743) | Variation of constants |
| Proposition | `diff:prop:polyforcing` (line 2794) | Polynomial forcing, and a terminating inverse |
| Lemma | `diff:lem:kernels` (line 2835) | Kernels of powers and real shifts |
| Theorem | `diff:thm:constant` (line 2866) | Constant-coefficient solution classification |
| Corollary | `diff:cor:matrix` (line 2940) | Constant matrix systems |
| Theorem | `diff:thm:triangular` (line 2981) | Triangular fundamental-matrix criterion |
| Proposition | `diff:prop:trace` (line 3017) | The trace test is necessary and not sufficient |
| Lemma | `diff:lem:matseparation` (line 3108) | The rank-one separation test |
| Corollary | `diff:cor:obsorder` (line 3123) | The obstruction preserves order |
| Theorem | `diff:thm:matsurjectivity` (line 3197) | Imported: splitting and first-order surjectivity, transferred |
| Lemma | `diff:lem:matcyclic` (line 3242) | Cyclic vector, and a rank-one filtration |
| Theorem | `diff:thm:matnormal` (line 3272) | Complete phase normal form for finite systems |
| Corollary | `diff:cor:matinhom` (line 3335) | Existence for every forcing, and the exact kernel dimension |
| Proposition | `diff:prop:matprojectors` (line 3369) | Canonical phase projectors |
| Corollary | `diff:cor:mattrace` (line 3400) | The determinant sees only the phase sum |
| Theorem | `diff:thm:matmetric` (line 3441) | The complete metric cone |
| Theorem | `diff:thm:matunitary` (line 3489) | Unitary phase normal form |
| Lemma | `diff:lem:matminmax` (line 3526) | Finite spectral theorem with attained min--max |
| Lemma | `diff:lem:matweyl` (line 3550) | An entrywise Weyl bound, and its ideal form |
| Lemma | `diff:lem:matboundedgauge` (line 3575) | Bounded-gauge estimate |
| Theorem | `diff:thm:matspectral` (line 3604) | Spectral--integral classification of Hermitian systems |
| Corollary | `diff:cor:matperturbation` (line 3667) | Finite-primitive perturbation invariance, with no gap hypothesis |
| Corollary | `diff:cor:matkernel` (line 3678) | Exact kernel count |
| Proposition | `diff:prop:sharpperturb` (line 3701) | Sharpness of the perturbation class |
| Theorem | `diff:thm:matnonabelian` (line 3827) | Normalized compact integration |
| Theorem | `diff:thm:matreal` (line 3940) | Real rotation-block classification |
| Theorem | `diff:thm:matrealmetric` (line 3979) | The real metric cone and its parity |
| Theorem | `diff:thm:matpinney` (line 4033) | Positive Pinney existence and uniqueness |
| Theorem | `diff:thm:matamplitude` (line 4119) | Canonical amplitude--phase reduction |
| Theorem | `diff:thm:matresonance` (line 4281) | The resonance algebra |
| Corollary | `diff:cor:mattorus` (line 4381) | Every finite system has a phase torus |
| Proposition | `diff:prop:matPValgebra` (line 4404) | The group algebra of the phase lattice, and its real form |
| Proposition | `diff:prop:hahnderiv` (line 4560) | The derivation on a real-exponent workspace |
| Corollary | `diff:cor:valphase` (line 4629) | A valuation test, on real exponents only |
| Theorem | `diff:thm:resolvent` (line 4662) | First-order resolvent on a real-exponent workspace |
| Proposition | `diff:prop:polyresolvent` (line 4704) | Polynomial Laurent inverse |
| Proposition | `diff:prop:factorialambiguity` (line 4788) | Uniqueness depends on the ambient field |
| Theorem | `diff:thm:factorial` (line 4816) | An exact factorially divergent forced oscillator |
| Theorem | `diff:thm:Hahnintegral` (line 4923) | Exact derivative image: one resonant coefficient |
| Theorem | `diff:thm:Hahnlogder` (line 4945) | Exact logarithmic-derivative image in $\Hring$ |
| Proposition | `diff:prop:Hahnambient` (line 4978) | Workspace versus ambient |
| Lemma | `diff:lem:monomialcriterion` (line 5064) | Monomial criterion |
| Theorem | `diff:thm:hull` (line 5084) | Differential Hahn hull |
| Proposition | `diff:prop:realgroup` (line 5144) | The real-exponent case, exactly |
| Theorem | `diff:thm:localize` (line 5184) | Closure localization |
| Theorem | `diff:thm:PVone` (line 5318) | Adjoining one missing rank-one solution |
| Theorem | `diff:thm:extension` (line 5362) | The same extension, with differential simplicity |
| Theorem | `diff:thm:PVlocal` (line 5406) | Over a localized workspace |
| Theorem | `diff:thm:PVhahn` (line 5431) | Over the rational Hahn field |
| Theorem | `diff:thm:PVrational` (line 5477) | Over the rational function field $\C(X)$ |
| Lemma | `diff:lem:rationallogder` (line 5487) | Untitled |
| Corollary | `diff:cor:nonembedding` (line 5516) | No differential embedding |
| Proposition | `diff:prop:oscillatorExtension` (line 5586) | A genuine oscillator |
| Theorem | `diff:thm:orderobstruction` (line 5648) | Oscillation cannot retain the $H$-field ordering rule |
| Lemma | `diff:lem:saturated` (line 5697) | The lattice is saturated |
| Theorem | `diff:thm:torus` (line 5710) | The diagonal phase torus |
| Lemma | `diff:rs:lem:euler` (line 5941) | The Euler derivation on real-exponent Hahn fields |
| Lemma | `diff:rs:lem:words` (line 6167) | Finite words at a fixed weight, with a length bound |
| Corollary | `diff:rs:cor:support` (line 6202) | Products, geometric inverses, and well-founded recursion |
| Lemma | `diff:rs:lem:critical` (line 6228) | Finite dependence at finitely many weights |
| Theorem | `diff:rs:thm:normal` (line 6305) | Normalized resonant form |
| Theorem | `diff:rs:thm:finite` (line 6379) | Finite resonance theorem |
| Corollary | `diff:rs:cor:replacement` (line 6414) | Gauge-equivalent finite coefficient replacement |
| Corollary | `diff:rs:cor:cutoff` (line 6438) | A useful but weaker cutoff statement |
| Theorem | `diff:rs:thm:constantform` (line 6470) | Constant frequency-and-nilpotent form |
| Lemma | `diff:rs:lem:eulermode` (line 6516) | Euler modes |
| Theorem | `diff:rs:thm:selection` (line 6556) | Spectral selection and explicit solution envelope |
| Corollary | `diff:rs:cor:invariance` (line 6593) | Perturbation invariance in the specified sector |
| Corollary | `diff:rs:cor:real` (line 6605) | Real systems |
| Theorem | `diff:rs:thm:Kclass` (line 6635) | Classification over the power-Hahn field |
| Corollary | `diff:rs:cor:HomK` (line 6672) | Exact morphism dimensions over $\KR$ |
| Theorem | `diff:rs:thm:SCclass` (line 6694) | Classification over the whole surcomplex field |
| Corollary | `diff:rs:cor:tensor` (line 6755) | Solution dimensions of tensor products |
| Proposition | `diff:rs:prop:phasespectrum` (line 6785) | An explicit non-Hermitian sector of the phase spectrum |
| Theorem | `diff:rs:thm:Hahnsol` (line 6856) | The Hahn solution space |
| Lemma | `diff:rs:lem:tautrans` (line 6874) | The logarithm is transcendental over $\KR$ |
| Theorem | `diff:rs:thm:minlog` (line 6900) | Minimal logarithmic repair |
| Theorem | `diff:rs:thm:forced` (line 6957) | Exact Hahn obstruction sequence |
| Theorem | `diff:rs:thm:workspace` (line 7155) | Finite-monomial and one-logarithm envelope |
| Proposition | `diff:rs:prop:boundary` (line 7247) | Infinitesimal coefficient, zero residue, no solution |
| Lemma | `diff:aut:lem:small` (line 7525) | Finite coordinates have infinitesimal derivatives |
| Lemma | `diff:aut:lem:evaluation` (line 7543) | Formal evaluation and the chain rule |
| Lemma | `diff:aut:lem:implicit` (line 7601) | Formal implicit uniqueness in a monad |
| Lemma | `diff:aut:lem:log` (line 7630) | Strip logarithms, for every normalized derivation |
| Theorem | `diff:aut:thm:main` (line 7707) | Autonomous realization classification |
| Lemma | `diff:aut:lem:projective` (line 7743) | Reduction of projective points |
| Lemma | `diff:aut:lem:zero` (line 7797) | A nonconstant trajectory reduces to a zero |
| Lemma | `diff:aut:lem:eigen` (line 7820) | Constant-coefficient eigenvectors |
| Proposition | `diff:aut:prop:simple` (line 7843) | Linearization and all simple-zero solutions |
| Lemma | `diff:aut:lem:leading` (line 7915) | The leading scale is forced |
| Proposition | `diff:aut:prop:multiple` (line 7961) | Existence, uniqueness and completeness at a multiple zero |
| Theorem | `diff:aut:thm:scales` (line 8104) | Uniform finite-scale localization |
| Corollary | `diff:aut:cor:independent` (line 8187) | A continuum of independent solutions inside two scales |
| Theorem | `diff:aut:thm:independence` (line 8228) | Derivation-independent autonomous sector |
| Corollary | `diff:aut:cor:scalarbound` (line 8305) | Uniform scalar bound |
| Corollary | `diff:aut:cor:realindep` (line 8338) | Real autonomous equations |
| Corollary | `diff:aut:cor:earlier` (line 8349) | Two earlier corollaries hold for every normalized derivation |
| Corollary | `diff:aut:cor:realbranches` (line 8388) | Exact real branch count |
| Proposition | `diff:aut:prop:contraction` (line 8466) | Infinitesimal contraction |
| Corollary | `diff:aut:cor:dual` (line 8481) | Holomorphic dual obstruction |
| Theorem | `diff:aut:thm:hyperelliptic` (line 8495) | Squarefree hyperelliptic obstruction |
| Lemma | `diff:aut:lem:formallog` (line 8552) | Normalized formal-group logarithm |
| Proposition | `diff:aut:prop:abeliansplit` (line 8583) | Global splitting through the identity monad |
| Theorem | `diff:aut:thm:abelianimage` (line 8622) | Abelian logarithmic-derivative image |
| Corollary | `diff:aut:cor:abeliancriterion` (line 8679) | Finite-primitive criterion for abelian motion; surjective $\Dn$ |
| Corollary | `diff:aut:cor:speeds` (line 8704) | Sharp one-power speed threshold; $\Dn=\der$ |
| Proposition | `diff:cp:prop:tower` (line 8997) | The ordinal log-atomic tower: imported |
| Lemma | `diff:cp:lem:scales` (line 9050) | Separation of scales |
| Lemma | `diff:cp:lem:triangular` (line 9083) | Summation and triangular differentiation |
| Theorem | `diff:cp:thm:critical` (line 9128) | Exact critical solutions and Wronskian |
| Lemma | `diff:cp:lem:span` (line 9169) | A fundamental pair spans every solution |
| Corollary | `diff:cp:cor:nonreal` (line 9192) | No nonreal powers of an infinite scale |
| Lemma | `diff:cp:lem:gauge` (line 9226) | Liouville transformation as an operator identity |
| Proposition | `diff:cp:prop:euler` (line 9254) | Euler classification at a positive infinite scale |
| Theorem | `diff:cp:thm:main` (line 9345) | Transfinite critical classification |
| Proposition | `diff:cp:prop:earlier` (line 9481) | The exact earlier-stage asymptotics |
| Theorem | `diff:cp:thm:invisible` (line 9498) | No set of earlier scales decides solvability |
| Proposition | `diff:cp:prop:noend` (line 9544) | There is no all-ordinal critical potential |
| Lemma | `diff:cp:lem:exponents` (line 9602) | Bounded support in the exponent group |
| Proposition | `diff:cp:prop:fieldclosure` (line 9626) | Derivative stability is a support assertion |
| Theorem | `diff:cp:thm:fieldjump` (line 9653) | Zero, one and two solutions over closed Hahn fields |
| Proposition | `diff:cp:prop:gaps` (line 9674) | An exponential gap followed by a primitive gap |
| Lemma | `diff:cp:lem:algind` (line 9735) | Algebraic independence of the two generators |
| Theorem | `diff:cp:thm:pv` (line 9748) | Borel differential Galois group |
| Corollary | `diff:cp:cor:additive` (line 9792) | After the first Hahn enlargement |
| Lemma | `diff:cp:lem:schwarzian` (line 9831) | Schwarzian and a normalized fundamental pair |
| Corollary | `diff:cp:cor:schwarzian` (line 9854) | Transfinite Schwarzian potentials |
| Theorem | `diff:thm:coherentlinear` (line 10099) | Positive-perturbation fundamental matrix |
| Corollary | `diff:cor:coherentinhom` (line 10164) | Inhomogeneous coherent systems |
| Corollary | `diff:cor:determinant` (line 10182) | Liouville determinant identity |
| Proposition | `diff:prop:negativecoherent` (line 10199) | A negative leading exponent forbids a coherent scalar exponential |
| Lemma | `diff:lem:nonlinear` (line 10266) | Admissibility of nonlinear evaluation |
| Theorem | `diff:thm:ivp` (line 10296) | Support-certified positive-support initial-value problem |
| Theorem | `diff:thm:monodromy` (line 10491) | Monodromy valued in $\GL_{d}(K_{\Gamma})$ |
| Proposition | `diff:prop:formalrecursion` (line 10623) | Formal existence over any characteristic-zero field |
| Lemma | `diff:lem:finiteincoming` (line 10676) | Finite incoming contributions |
| Theorem | `diff:thm:coefderivation` (line 10690) | Differentiation preserves common-domain coherence |
| Theorem | `diff:thm:totalchainhalo` (line 10739) | Total intrinsic derivative of an evaluation |
| Corollary | `diff:cor:naturality` (line 10804) | Coefficientwise linear naturality |
| Lemma | `diff:lem:twosupports` (line 12497) | Sum of two supports |
| Lemma | `diff:lem:higman` (line 12526) | Finite-word lemma |

### dynamics-and-normal-forms

Source: [surcomplex/dynamics-and-normal-forms/article.tex](surcomplex/dynamics-and-normal-forms/article.tex).

Statements in this newly indexed report remain **pending unless mapped above**.
The finite-word Neumann support lemma and the combinatorial bounds below
are checked; the manuscript correction is recorded separately from that coverage.

**Corrected in the maintained report:** `dyn:cor:ancestry` now retains the
input support `B = supp A`. Its finite pairs `(b,w)` satisfy `b + sum w = γ`,
and its depth bound is `ell_{B,S}(γ)`. The expanded proof counts consecutive
nonempty blocks of each word, establishing strong summability of the operator
iterates and of jointly summable input families under the explicit linear
positive-word hypothesis. The earlier input-independent bound was false:
with `Γ = ℤ`, `S = {1}`, `T(A) = t A`, the input `t^(-n)` contributes
`T^n(t^(-n)) = 1` at output zero, where `ell_S(0) = 0`.
The counterexample and corrected combinatorial bounds are checked in
[Ancestry.lean](../Surreal/HahnSeries/Ancestry.lean); the full operator statement
and downstream analytic results still require separate formal proofs.
The stronger bound in `dyn:prop:linearization` remains valid because its
initial input `L⁻¹f` supplies an initial positive support letter.
The merged report and its README explicitly record this correction; the
original source 03 already retained arbitrary input support in its finite-
dependence claim, and remains accessible in Git history.

The expansion adds 16 pending obligations for resonance flags, fixed-strip
small-divisor solvability and nonlinear normal forms. The external torus
derivatives annihilate Hahn scalars and are distinct from the scalar surreal
derivation. Joint support control and the exact arithmetic hypotheses remain
required beyond the finite-word support lemmas already checked.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `dyn:lem:neumann` (line 1202) | Positive-support lemma of Neumann, in finite-word form |
| Corollary | `dyn:cor:ancestry` (line 1265) | Finite ancestry relative to the input support |
| Lemma | `dyn:lem:evaluation` (line 1398) | Evaluation, inversion, isometry |
| Proposition | `dyn:prop:eval` (line 1458) | Faithful analytic realization |
| Lemma | `dyn:lem:faithful` (line 1491) | Faithfulness of infinitesimal evaluation |
| Proposition | `dyn:prop:subgroup` (line 1530) | Substitution group |
| Lemma | `dyn:lem:inverse` (line 1579) | Near-identity inverses |
| Theorem | `dyn:thm:exp-log` (line 1609) | Same-domain exponential--logarithm correspondence |
| Lemma | `dyn:lem:fixedderivative` (line 1698) | Derivative of the logarithmic generator at an ordinary fixed point |
| Corollary | `dyn:cor:julia` (line 1720) | Julia equation |
| Proposition | `dyn:prop:intertwine` (line 1729) | Conjugacy and vector fields |
| Corollary | `dyn:cor:flow` (line 1743) | Exact flow law and admissible Hahn times |
| Corollary | `dyn:cor:roots` (line 1776) | Unique fractional iteration; torsion-freeness |
| Theorem | `dyn:thm:fixed-ideal` (line 1796) | Fixed-point ideal of a positive flow |
| Theorem | `dyn:thm:centralizer` (line 1846) | The full positive centralizer in one variable |
| Proposition | `dyn:prop:workspace` (line 1910) | Workspace invariance |
| Lemma | `dyn:lem:radius-loss` (line 1963) | Single-step analytic loss |
| Lemma | `dyn:lem:sharp-divisor` (line 1983) | Sharpness and analytic failure |
| Proposition | `dyn:prop:norm` (line 2026) | A compact-disk estimate, offered only as a starting point |
| Theorem | `dyn:thm:main` (line 2061) | Universal coefficient-category classification |
| Proposition | `dyn:prop:linearization` (line 2120) | Support-controlled inverse; route A |
| Theorem | `dyn:thm:lifting` (line 2164) | Support-controlled lifting; route B, drift permitted |
| Proposition | `dyn:prop:reusable` (line 2256) | Reusable abstract form |
| Proposition | `dyn:prop:first-weight` (line 2285) | The first-weight obstruction |
| Corollary | `dyn:cor:entirethreshold` (line 2335) | The entire-coefficient threshold; polynomial universality |
| Theorem | `dyn:thm:radius-depth` (line 2352) | Radius at a specified Hahn exponent |
| Theorem | `dyn:thm:degrees` (line 2401) | Polynomial coefficient degrees |
| Proposition | `dyn:prop:halo` (line 2447) | Actual conjugacy on a finite halo |
| Proposition | `dyn:prop:monad` (line 2466) | The monad needs no arithmetic |
| Lemma | `dyn:lem:multihomological` (line 2504) | Multivariable homological inverse |
| Theorem | `dyn:thm:multilifting` (line 2520) | Multivariable support-controlled lifting |
| Theorem | `dyn:thm:commoncoord` (line 2555) | A common coordinate for the centralizer |
| Lemma | `dyn:esm:lem:cluster` (line 2679) | One rational cluster; sources 08 and 09 |
| Lemma | `dyn:esm:lem:packing` (line 2710) | Divisible-subtree packing; sources 08 and 09 |
| Theorem | `dyn:esm:thm:treebound` (line 2750) | Tree product bound; source 09 |
| Corollary | `dyn:esm:cor:chain` (line 2773) | Strict chains and the fixed-complexity rate; sources 08 and 09 |
| Lemma | `dyn:esm:lem:degreechain` (line 2856) | Strict degree chains; source 08 |
| Proposition | `dyn:esm:prop:coefbound` (line 2909) | A depth-uniform exponential rate; source 08 |
| Corollary | `dyn:esm:cor:commondomain` (line 2945) | One open polydisk for every coefficient; source 08 |
| Theorem | `dyn:esm:thm:main` (line 2965) | Sharp common domain for an exact scalar multiplier; sources 08 and 09 |
| Corollary | `dyn:esm:cor:sixthrow` (line 3033) | The sixth category for a scalar exact multiplier; sources 08 and 09 |
| Proposition | `dyn:tree:prop:formula` (line 3154) | Plane-tree coefficient formula; source 09 |
| Lemma | `dyn:tree:lem:count` (line 3183) | Polynomial tree count; source 09 |
| Proposition | `dyn:tree:prop:estimate` (line 3202) | Finite-depth estimate for the forward coordinate; source 09 |
| Corollary | `dyn:esm:cor:parameters` (line 3241) | Several formal parameters, one dynamical variable; source 09 |
| Theorem | `dyn:nsc:thm:main` (line 3468) | Common-domain linearization for a nonscalar exact multiplier; source 10 |
| Lemma | `dyn:nsc:lem:height` (line 3510) | Exponential rates and integer height; source 10 |
| Corollary | `dyn:nsc:cor:angular` (line 3561) | Angular-rank form; source 10 |
| Lemma | `dyn:nsc:lem:blocks` (line 3613) | Marked-block contraction; source 10 |
| Theorem | `dyn:nsc:thm:products` (line 3671) | Rational-rank divisor-product bound; source 10 |
| Corollary | `dyn:nsc:cor:rankone` (line 3736) | The fixed-complexity rate in angular rank one; source 10 |
| Proposition | `dyn:nsc:prop:formal` (line 3794) | Colored tree expansion of the forward coordinate; source 10 |
| Lemma | `dyn:nsc:lem:count` (line 3829) | Polynomial diagram count; source 10 |
| Corollary | `dyn:nsc:cor:local` (line 3887) | Input-relative radius at a specified exponent; source 10 |
| Corollary | `dyn:nsc:cor:parameters` (line 3914) | Rectangular polydisks and ordinary parameters; source 10 |
| Theorem | `dyn:nsc:thm:criterion` (line 3974) | Exact criterion and rank-one sharpness; source 10 |
| Proposition | `dyn:nsc:prop:twomode` (line 4033) | Two modes in one irrational direction; source 10 |
| Lemma | `dyn:lem:jets` (line 4206) | Uniform reciprocal-jet estimates |
| Theorem | `dyn:thm:collapse` (line 4236) | Exact coefficient-radius collapse; requires drift |
| Corollary | `dyn:cor:finitefailure` (line 4301) | A finite-support instability |
| Theorem | `dyn:thm:trichotomy` (line 4312) | The common-domain / radius-free trichotomy |
| Theorem | `dyn:thm:multicollapse` (line 4380) | Exact multivariable radius collapse |
| Proposition | `dyn:prop:cf` (line 4437) | Continued-fraction formula |
| Theorem | `dyn:thm:nonbrjuno` (line 4470) | Explicit arithmetic separations |
| Lemma | `dyn:cyc:lem:chains` (line 4587) | Pole multiplicity after collisions; source 08 |
| Lemma | `dyn:cyc:lem:majorant` (line 4614) | Polynomial numerators at fixed parameter degree; source 08 |
| Proposition | `dyn:cyc:prop:upper` (line 4634) | The upper bound under drift; source 08 |
| Proposition | `dyn:cyc:prop:noncancel` (line 4670) | Collision noncancellation at convergent degrees; source 08 |
| Theorem | `dyn:cyc:thm` (line 4700) | Sharp collapse with one cyclic exponent; \textbf{requires drift}; source 08 |
| Corollary | `dyn:cyc:cor:classification` (line 4753) | No independent scales are needed; source 08 |
| Corollary | `dyn:cyc:cor:onecoef` (line 4792) | One positive Hahn coefficient suffices; source 08 |
| Lemma | `dyn:lem:nonresonant` (line 4966) | Nonresonant residue |
| Lemma | `dyn:lem:displacement` (line 4995) | Divisible displacement: cancelling a common infinitesimal divisor |
| Lemma | `dyn:lem:root-count` (line 5031) | Roots on the unit shell |
| Theorem | `dyn:thm:exact` (line 5059) | Exact finite-return linearization |
| Theorem | `dyn:thm:shell` (line 5173) | Resonant shell cycles |
| Corollary | `dyn:cor:finite-certificate` (line 5219) | A finite obstruction certificate |
| Theorem | `dyn:thm:stability` (line 5235) | Stability above the first return face |
| Theorem | `dyn:thm:coherent` (line 5298) | Coherent realization of resonant linearization |
| Proposition | `dyn:prop:leading` (line 5403) | The leading-coefficient exponential integral |
| Proposition | `dyn:prop:noncoherent` (line 5469) | A divergent ordinary linearizer survives on the monad |
| Theorem | `dyn:thm:workspace` (line 5516) | Workspace invariance for the finite-return package |
| Corollary | `dyn:cor:surcomplex` (line 5545) | Transfer to the surcomplex numbers |
| Theorem | `dyn:thm:phase` (line 5654) | Cancellation phase diagram |
| Lemma | `dyn:lem:unit` (line 5805) | A sufficient unit criterion |
| Theorem | `dyn:thm:common` (line 5823) | Common-domain Hahn linearization |
| Corollary | `dyn:cor:universal` (line 5899) | Universal leading profile at a resonant scale |
| Proposition | `dyn:prop:factorV` (line 5938) | The generator gains no new pole |
| Lemma | `dyn:lem:residue` (line 5976) | Exact residue at a simple fixed point |
| Proposition | `dyn:prop:firstcorrection` (line 5996) | The first correction is an explicit logarithm |
| Corollary | `dyn:cor:factorization` (line 6016) | Separation of the branching factors |
| Lemma | `dyn:lem:torsion` (line 6049) | An infinitesimal phase has no torsion |
| Theorem | `dyn:thm:monodromy` (line 6070) | Exact monodromy and obstruction to finite ramification |
| Lemma | `dyn:lem:slopes` (line 6105) | A nonlinear polynomial cannot have one slope at all its zeros |
| Lemma | `dyn:lem:reduction` (line 6120) | Reduction of an algebraic Hahn element |
| Lemma | `dyn:lem:essential` (line 6134) | A higher-order logarithmic pole forces transcendence |
| Theorem | `dyn:thm:dichotomy` (line 6153) | Polynomial Euler maps: the algebraicity dichotomy |
| Proposition | `dyn:prop:leadingalgebraic` (line 6216) | Classification of algebraic leading coordinates |
| Proposition | `dyn:prop:recurrence` (line 6304) | Exact finite recurrence |
| Theorem | `dyn:thm:sharp` (line 6333) | Sharp domain and valuative isometry |
| Theorem | `dyn:thm:modelfactor` (line 6433) | All-orders factorization and finite-cover obstruction for the model |
| Proposition | `dyn:prop:second` (line 6471) | Explicit second-order expansion |
| Lemma | `dyn:lem:primitive` (line 6592) | Support-preserving primitives |
| Lemma | `dyn:lem:homotopy` (line 6622) | Explicit exactness of an infinitesimal pullback |
| Proposition | `dyn:prop:time-conjugacy` (line 6656) | Time forms under conjugacy |
| Theorem | `dyn:thm:difference` (line 6679) | Discrete equation as a primitive problem |
| Corollary | `dyn:cor:abel` (line 6727) | Exact global Abel criterion |
| Theorem | `dyn:thm:exact-sequence` (line 6750) | Complete finite-dimensional discrete obstruction |
| Lemma | `dyn:lem:displacement2` (line 6827) | Implicit displacement lemma |
| Theorem | `dyn:thm:classification` (line 6875) | Complete period invariant and marked conjugacy |
| Corollary | `dyn:cor:simplyconnected` (line 6916) | Simply connected domains |
| Theorem | `dyn:thm:moduli` (line 6949) | An explicit moduli space |
| Theorem | `dyn:thm:flat` (line 7023) | Flatly indistinguishable but globally nonconjugate |
| Proposition | `dyn:prop:euler-residue` (line 7144) | Exact residue of the Euler time form |
| Corollary | `dyn:cor:euler-normal` (line 7202) | A global coherent normal form for the Euler family |
| Theorem | `dyn:thm:slowtime` (line 7281) | Common-chart Hahn lifting of the slow flow |
| Proposition | `dyn:prop:inverse` (line 7405) | Positive near-identity maps |
| Proposition | `dyn:prop:exp` (line 7429) | Supported Hamiltonian exponential |
| Lemma | `dyn:lem:projection` (line 7487) | Entire action projection |
| Theorem | `dyn:thm:homological` (line 7507) | Sharp homological criterion |
| Theorem | `dyn:thm:normalform` (line 7555) | Exact positive-Hahn normal form |
| Corollary | `dyn:cor:hamsurcomplex` (line 7656) | Finite surcomplex phase space |
| Theorem | `dyn:thm:integrability` (line 7684) | Exact integrability |
| Theorem | `dyn:thm:pcentralizer` (line 7705) | Poisson centralizer |
| Proposition | `dyn:prop:flow` (line 7747) | Exact ordinary-time evolution |
| Theorem | `dyn:thm:universal` (line 7785) | Sharp universal normalization criterion |
| Proposition | `dyn:prop:explicitbad` (line 7826) | An explicit super-Liouville obstruction |
| Theorem | `dyn:thm:rescale` (line 7941) | Compatible support-certified domains |
| Corollary | `dyn:cor:homogeneous` (line 8013) | A degree-dependent radius |
| Proposition | `dyn:prop:discrete` (line 8169) | Polynomial-layer linearization |
| Lemma | `dyn:lem:qpmultiplier` (line 8317) | Subexponential Fourier multipliers |
| Lemma | `dyn:lem:qpsubstitution` (line 8330) | Taylor substitution on the torus, with its Lipschitz estimate |
| Theorem | `dyn:thm:flag` (line 8406) | Finite flag and one common reciprocal support |
| Proposition | `dyn:prop:qpjets` (line 8487) | Coefficient structure of the inverse |
| Proposition | `dyn:prop:qpvalbound` (line 8519) | An arithmetic-free valuation bound |
| Theorem | `dyn:thm:qplinear` (line 8619) | Universal fixed-strip solvability |
| Corollary | `dyn:cor:qpsharp` (line 8693) | The divisor loss $\kups$ is attained |
| Corollary | `dyn:cor:qptail` (line 8717) | Higher tails do not change the arithmetic test |
| Theorem | `dyn:thm:qpjet` (line 8764) | Arbitrary finite analytic lifting, but no full lift |
| Theorem | `dyn:thm:qpnormalform` (line 8864) | Hahn-analytic constant normal form |
| Lemma | `dyn:lem:qpcoordinverse` (line 9018) | Infinitesimal coordinate inverses on the torus |
| Theorem | `dyn:thm:qpnecessity` (line 9055) | Non-linearizable perturbations beyond any prescribed valuation |
| Corollary | `dyn:cor:qpequivalence` (line 9093) | Exact universal infinitesimal normal-form criterion |
| Proposition | `dyn:prop:qpboundary` (line 9103) | Failure exactly at the threshold, with no zero of the slow speed |
| Lemma | `dyn:lem:qpchangevar` (line 9149) | Formal change of variables |
| Theorem | `dyn:thm:qpdensity` (line 9176) | Invariant density and its uniqueness |
| Theorem | `dyn:thm:finite-order` (line 9380) | Same-domain finite-order decomposition |
| Proposition | `dyn:prop:quadratic-scale` (line 9463) | Quadratic scaling and the boundary of the halo theorem |
| Proposition | `dyn:prop:critical` (line 9506) | A precise rescaled-germ obstruction |

### entire-functions-at-arbitrary-rank

Source: [surcomplex/entire-functions-at-arbitrary-rank/article.tex](surcomplex/entire-functions-at-arbitrary-rank/article.tex).

All statements in this report remain **pending unless explicitly mapped**.
The setting is a fixed set-sized Hahn field, not all actual surcomplex
numbers. The several-variable section states weaker group and coefficient
hypotheses than the divisible complex setting of the other sections. The proved
Hahn support, summability and algebraic-closure modules are prerequisites;
the cofinality/order-unit criteria, preparation, infinite products, ideal
classification and exact scalar-extension domain still need proofs. Any
whole-class corollary additionally needs the actual workspace bridge.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `ent:thm:main` (line 344) | Cofinality--rank trichotomy |
| Theorem | `ent:thm:main-image` (line 379) | Exact image of the infinite jet map |
| Theorem | `ent:thm:main-extension` (line 432) | Universal scalar-extension package |
| Lemma | `ent:lem:neumann` (line 650) | Hahn--Neumann support calculus |
| Lemma | `ent:lem:cofinal-tails` (line 671) | Cofinal tails |
| Theorem | `ent:thm:criterion` (line 915) | All-point strong summability |
| Corollary | `ent:cor:cofinality` (line 985) | Cofinality dichotomy |
| Proposition | `ent:prop:operations` (line 1014) | Entire operations |
| Theorem | `ent:thm:units` (line 1082) | Restricted-unit criterion |
| Corollary | `ent:cor:unit-structure` (line 1145) | Unit group of the restricted algebra |
| Lemma | `ent:lem:A-units` (line 1213) | Units and integral substitution |
| Theorem | `ent:thm:prep` (line 1242) | Support-controlled preparation |
| Corollary | `ent:cor:prep-extension` (line 1291) | The certificate survives enlargement of the value group |
| Corollary | `ent:cor:integral-zeros` (line 1356) | Finite zero geometry on the integral disk |
| Theorem | `ent:thm:roots` (line 1371) | Ball, shell, and residue-direction counts |
| Corollary | `ent:cor:units` (line 1409) | Units, faithfulness, and values |
| Lemma | `ent:lem:linear-division` (line 1430) | Division by a linear zero factor |
| Corollary | `ent:cor:stability` (line 1448) | Initial-form stability |
| Proposition | `ent:prop:newton` (line 1458) | Locally finite Newton profile |
| Lemma | `ent:lem:divisor-countable` (line 1506) | Countability and escape |
| Theorem | `ent:thm:product` (line 1531) | Canonical product for a radial divisor |
| Theorem | `ent:thm:factorization` (line 1576) | Factorization by zeros |
| Corollary | `ent:cor:gcd` (line 1625) | Divisibility, GCDs, and least common multiples |
| Corollary | `ent:cor:evaluation` (line 1648) | Finite jets and evaluation ideals |
| Corollary | `ent:cor:value-distribution` (line 1662) | Rigidity and value distribution |
| Corollary | `ent:cor:conjugation` (line 1694) | Conjugation and real-coefficient functions |
| Proposition | `ent:prop:nonnoetherian` (line 1708) | Untitled |
| Lemma | `ent:lem:escaping-classes` (line 1748) | Untitled |
| Lemma | `ent:lem:shells` (line 1774) | Shell decomposition |
| Lemma | `ent:lem:coarse-residue` (line 1857) | Coarsened residues |
| Theorem | `ent:thm:image` (line 1929) | Shellwise Hermite interpolation; the exact image |
| Theorem | `ent:thm:quotient` (line 1960) | The entire quotient is the restricted product |
| Proposition | `ent:prop:kernel-direct` (line 1993) | Principal vanishing ideal, second proof |
| Lemma | `ent:lem:integral` (line 2067) | Integral polynomial operations |
| Lemma | `ent:lem:assembly` (line 2106) | Assembly |
| Lemma | `ent:lem:damping-shell` (line 2189) | Uniform damping estimate |
| Corollary | `ent:cor:single-node` (line 2274) | Exact one-node interpolation |
| Corollary | `ent:cor:coarse-separated` (line 2295) | Coarsely separated shells |
| Corollary | `ent:cor:order-unit-image` (line 2316) | Order units and the disappearance of the restriction |
| Corollary | `ent:sm:cor:no-order-unit` (line 2335) | Without an order unit the restriction never disappears |
| Lemma | `ent:sm:lem:entire-sum` (line 2400) | Summing entire corrections |
| Lemma | `ent:sm:lem:inverse-shell` (line 2427) | Integral inverse of the cofactor |
| Lemma | `ent:sm:lem:cardinal` (line 2471) | Cardinal corrections |
| Corollary | `ent:sm:cor:error` (line 2531) | An explicit truncation certificate |
| Lemma | `ent:lem:growth-barrier` (line 2589) | Archimedean growth barrier, exact form |
| Corollary | `ent:cor:no-interpolation` (line 2651) | Explicit failure of value interpolation, and its exact boundary |
| Lemma | `ent:lem:shellunits` (line 2697) | Units of a shell algebra |
| Lemma | `ent:lem:restrictedunits` (line 2716) | Units of the restricted product |
| Theorem | `ent:thm:bezout-criterion` (line 2728) | Sharp B\'ezout criterion |
| Theorem | `ent:sm:thm:finite-generators` (line 2785) | Finitely many generators |
| Corollary | `ent:sm:cor:membership` (line 2842) | Membership, one simple node per shell |
| Theorem | `ent:thm:no-bezout` (line 2857) | An explicit pointwise B\'ezout failure |
| Theorem | `ent:sm:thm:paired` (line 2932) | The exact threshold for paired zeros |
| Theorem | `ent:thm:close-pair` (line 2970) | A close pair with individually harmless values |
| Corollary | `ent:cor:invisible-ideal` (line 3012) | A finitely generated ideal invisible to point tests |
| Theorem | `ent:thm:maximal` (line 3059) | Explicit non-evaluation maximal ideals |
| Corollary | `ent:cor:residue-fields` (line 3114) | Finite-rank residue fields in an infinite-rank example |
| Theorem | `ent:sm:thm:maximal-all` (line 3175) | Every maximal ideal above $P_D$ |
| Theorem | `ent:sm:thm:beta` (line 3223) | The maximal spectrum of the quotient |
| Corollary | `ent:sm:cor:boundary-pair` (line 3254) | The whole maximal-ideal locus of a paired example |
| Corollary | `ent:sm:cor:boundary-fields` (line 3279) | Algebraic type of the residue fields |
| Proposition | `ent:sm:prop:transcendental` (line 3296) | A transcendental boundary coordinate |
| Proposition | `ent:prop:real-form` (line 3347) | Real form |
| Lemma | `ent:lem:coarsening` (line 3412) | Real-valued coarsening |
| Theorem | `ent:thm:interpolation` (line 3487) | Arbitrary radial Hermite interpolation |
| Theorem | `ent:thm:bezout` (line 3582) | B\'ezout in the order-unit case |
| Theorem | `ent:thm:extension-criterion` (line 3647) | Sharp change-of-workspace criterion |
| Lemma | `ent:lem:coarsened-ring` (line 3692) | Untitled |
| Theorem | `ent:thm:extension` (line 3724) | Universal scalar-extension domain |
| Corollary | `ent:cor:entire-extension` (line 3756) | Cofinal extensions are exactly the entire extensions |
| Theorem | `ent:thm:zero-conservation` (line 3792) | Zero conservation under arbitrary enlargement |
| Proposition | `ent:prop:identity` (line 3824) | Identity on constants |
| Theorem | `ent:thm:no-continuation` (line 3840) | Obstruction to any entire-series continuation |
| Corollary | `ent:cor:intrinsic-boundary` (line 3861) | Intrinsic description of the extension boundary |
| Corollary | `ent:cor:no-repair` (line 3887) | No repair of the counterexample by a Hahn extension |
| Corollary | `ent:cor:all-no` (line 3907) | Whole-class rigidity on the surcomplex numbers |
| Lemma | `ent:mv:lem:tails` (line 4025) | Tail certificate and regrouping |
| Theorem | `ent:thm:multi-criterion` (line 4064) | Finite-variable coefficient criterion |
| Proposition | `ent:mv:prop:realize-support` (line 4113) | Every ordinary support occurs |
| Theorem | `ent:thm:multi-unit` (line 4149) | Untitled |
| Lemma | `ent:mv:lem:twist` (line 4181) | Uniform unit twisting |
| Lemma | `ent:mv:lem:lattice` (line 4209) | The finite lattice estimate |
| Theorem | `ent:mv:thm:domain` (line 4232) | Exact multivariate extension domain |
| Corollary | `ent:mv:cor:tails` (line 4300) | Independence of tails within the entire category |
| Corollary | `ent:mv:cor:onevar` (line 4320) | The one-variable domain, recovered |
| Proposition | `ent:mv:prop:cone` (line 4345) | Cone and monotonicity properties |
| Proposition | `ent:mv:prop:algebra` (line 4371) | Evaluation algebras at a fixed point |
| Theorem | `ent:mv:thm:semilinear` (line 4391) | The period-inequality criterion |
| Theorem | `ent:mv:thm:nonclosed` (line 4423) | A nonclosed domain in two variables |
| Proposition | `ent:mv:prop:linear` (line 4489) | Linear covariance |
| Theorem | `ent:mv:thm:rays` (line 4521) | Polynomial rays and new scales |
| Proposition | `ent:mv:prop:coordinate` (line 4551) | Directions for the whole family |
| Proposition | `ent:mv:prop:coordinate-realize` (line 4569) | Realizing the coordinate pattern |
| Theorem | `ent:mv:thm:exceptional` (line 4606) | Necessary form and generic obstruction |
| Theorem | `ent:mv:thm:realization` (line 4654) | Exact realization of the exceptional locus |
| Corollary | `ent:mv:cor:countable` (line 4682) | Sharp two-variable classification |
| Lemma | `ent:mv:lem:localize` (line 4730) | Localization of the data |
| Corollary | `ent:mv:cor:surcomplex` (line 4748) | Surcomplex support-domain theorem |
| Proposition | `ent:mv:prop:allscale` (line 4783) | Whole-class rigidity in both conventions |
| Theorem | `ent:thm:infinite-example` (line 4993) | A genuine infinite-rank surcomplex entire function |

### finite-deformations

Source: [surcomplex/finite-deformations/article.tex](surcomplex/finite-deformations/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `finite:lem:support` (line 292) | Hahn--Neumann support lemma |
| Lemma | `finite:lem:operator` (line 320) | Support-controlled operator inversion |
| Proposition | `finite:prop:evaluation` (line 364) | Evaluation is a homomorphism |
| Lemma | `finite:lem:shifted` (line 380) | Shifted division and finite Taylor remainder |
| Lemma | `finite:lem:autosupport` (line 415) | Automatic common support |
| Theorem | `finite:thm:hartogs` (line 429) | Automatic Hahn--Hartogs coherence |
| Corollary | `finite:cor:hole` (line 449) | Coherent Hartogs removal |
| Lemma | `finite:lem:ordinarydivision` (line 486) | Uniform ordinary division operators |
| Theorem | `finite:thm:matrixdivision` (line 509) | Support-controlled matrix division |
| Theorem | `finite:thm:parameterprep` (line 541) | Fixed-domain Hahn preparation with holomorphic parameters |
| Corollary | `finite:cor:oneshrink` (line 570) | One shrink, and no more |
| Theorem | `finite:thm:hpl` (line 613) | Hahn contraction formula |
| Proposition | `finite:prop:ordinarykoszul` (line 681) | The ordinary quotient and its Koszul resolution |
| Theorem | `finite:thm:finitefree` (line 703) | Uniform finite-flat zero algebra; division with the $S+M$ certificate |
| Corollary | `finite:cor:koszul` (line 748) | Explicit lifting of Koszul relations |
| Corollary | `finite:cor:restriction` (line 771) | No loss of support under restriction |
| Theorem | `finite:thm:family` (line 802) | Perturbed monomial complete intersections, with holomorphic parameters |
| Theorem | `finite:thm:finitefree15` (line 856) | Finite-free complete intersections by matrix induction |
| Lemma | `finite:lem:coordpoly` (line 888) | Coordinate characteristic polynomials |
| Lemma | `finite:lem:matrix` (line 897) | Summable matrix functional calculus |
| Theorem | `finite:thm:characters` (line 910) | All characters are evaluations |
| Theorem | `finite:thm:length` (line 940) | Local algebra comparison and exact conservation |
| Corollary | `finite:cor:rouche` (line 964) | Conservation of multiplicity; a monad form of Rouch\'e |
| Corollary | `finite:cor:monadmap` (line 971) | Finite mapping of an entire monad |
| Lemma | `finite:lem:translation` (line 1013) | Evaluation, translation, division by coordinates |
| Theorem | `finite:thm:formaldivision` (line 1022) | Uniform-support division and conservation of colength over $\Af_{n,\Gamma}$ |
| Theorem | `finite:thm:localization` (line 1036) | Uniform valuation localization of the zeros |
| Theorem | `finite:thm:fibres` (line 1056) | Finite infinitesimal fibres |
| Corollary | `finite:cor:inverse` (line 1070) | A bijection of the whole monad, with fine-analytic inverse |
| Theorem | `finite:thm:monadcount` (line 1093) | Coherent conservation of isolated intersections |
| Theorem | `finite:thm:spectral` (line 1112) | Characteristic polynomials, traces and norms |
| Proposition | `finite:prop:separation` (line 1132) | A bounded list of separating linear forms |
| Proposition | `finite:prop:resdescend` (line 1185) | The residue descends to the finite algebra |
| Corollary | `finite:cor:coefficientresidue` (line 1196) | Explicit coefficient extraction for coordinate-power leading systems |
| Theorem | `finite:thm:duality` (line 1220) | Perfect integral residue duality |
| Corollary | `finite:cor:residuereconstruction` (line 1236) | Contour recovery of the finite algebra |
| Corollary | `finite:cor:relative` (line 1251) | Relative residue duality over a parameter domain |
| Lemma | `finite:lem:witness` (line 1281) | Finite-witness transfer |
| Lemma | `finite:lem:finitedependence` (line 1301) | The ordinary finite-parameter comparison |
| Theorem | `finite:thm:trace` (line 1313) | Trace--Jacobian identity and simple-zero residues |
| Theorem | `finite:thm:bezout` (line 1355) | Residue reproducing kernel |
| Theorem | `finite:thm:localres` (line 1399) | Moving-intersection residue theorem |
| Corollary | `finite:cor:transformation` (line 1419) | Change of generators |
| Theorem | `finite:thm:transform` (line 1428) | Coordinate change by an infinitesimal displacement |
| Theorem | `finite:thm:discriminant` (line 1448) | Discriminant--Jacobian identity and the reducedness criterion |
| Proposition | `finite:prop:univtrace` (line 1477) | One-variable trace and residue formulas, stable across collisions |
| Theorem | `finite:thm:monodromy` (line 1498) | Support-preserving lift of the ordinary root cover |
| Theorem | `finite:thm:precision` (line 1525) | Precision of normal forms, residues and spectral invariants |
| Corollary | `finite:cor:discstable` (line 1555) | A discriminant threshold that preserves simple zeros |
| Theorem | `finite:thm:rootstability` (line 1572) | Sharp conditioned root stability |
| Corollary | `finite:cor:matching` (line 1623) | Stable matching of an entire simple cluster |
| Proposition | `finite:prop:sharpness` (line 1632) | Both bounds attained, and the threshold strict |

### global-divisors

Source: [surcomplex/global-divisors/article.tex](surcomplex/global-divisors/article.tex).

The expansion adds 20 pending obligations on compact ordinary complex
curves. It requires common-domain Hahn coefficient sheaves, valuation
monodromy, finite cohomology models and classical Picard/Riemann–Roch/Abel
inputs. Integral truncation quotients and the full coefficient field must
remain distinct.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `global:lem:support` (line 250) | Support calculus |
| Proposition | `global:prop:evaluation` (line 298) | Evaluation and identity |
| Proposition | `global:prop:sheaf` (line 315) | Support-preserving sheaf property |
| Proposition | `global:prop:units` (line 327) | Exact unit criterion |
| Proposition | `global:prop:explog` (line 343) | Positive-support exponential and logarithm |
| Lemma | `global:lem:scalarML` (line 373) | Scalar Weierstrass and Mittag--Leffler |
| Lemma | `global:lem:hermite` (line 389) | Discrete Hermite interpolation |
| Lemma | `global:lem:scalarCousin` (line 410) | Scalar additive Cousin theorem on $\C$ |
| Theorem | `global:thm:preparation` (line 448) | Uniform-support local preparation |
| Corollary | `global:cor:roots` (line 481) | All roots in a monad |
| Lemma | `global:lem:division` (line 497) | Deformed division |
| Lemma | `global:lem:polefree` (line 521) | Pole-free fractions |
| Theorem | `global:thm:PID` (line 535) | Principal-ideal-domain stalks |
| Proposition | `global:prop:nonlocal` (line 557) | Non-locality, and the integral model |
| Corollary | `global:cor:Picmeaning` (line 571) | Meaning of the Picard group over the plane |
| Theorem | `global:thm:ML` (line 615) | Uniform-support Mittag--Leffler criterion |
| Corollary | `global:cor:interp` (line 641) | Entire interpolation with an exact support criterion |
| Theorem | `global:thm:divisor` (line 661) | Sharp global moving-divisor criterion |
| Proposition | `global:prop:realizationtorsor` (line 715) | The freedom in realization |
| Corollary | `global:cor:splitting` (line 785) | Failure of arbitrary global divisor splitting |
| Proposition | `global:prop:restrictedalgebra` (line 819) | Restricted product algebra |
| Theorem | `global:thm:interpolation` (line 835) | Deformed Hermite interpolation |
| Corollary | `global:cor:CRT` (line 858) | Chinese remainder quotient |
| Theorem | `global:thm:MLmoving` (line 899) | Sharp moving-pole Mittag--Leffler theorem |
| Theorem | `global:thm:aut` (line 936) | Global inverse for positive-support perturbations |
| Corollary | `global:cor:motion` (line 960) | Exact interpolation of simple motions |
| Theorem | `global:thm:cousincriterion` (line 998) | Necessary and sufficient Cousin criterion |
| Theorem | `global:thm:obstruction` (line 1036) | A concrete obstruction subspace |
| Corollary | `global:cor:H1injection` (line 1063) | First cohomology detected by descending scales |
| Corollary | `global:cor:H1size` (line 1081) | Size and local invisibility |
| Proposition | `global:prop:divPic` (line 1108) | The divisor and logarithmic obstructions coincide |
| Proposition | `global:prop:Picreduction` (line 1122) | Reduction of the plane Picard group to positive supports |
| Lemma | `global:lem:descending` (line 1146) | Descending positive sequences |
| Theorem | `global:thm:dichotomy` (line 1154) | Picard-group vanishing dichotomy over the plane |
| Theorem | `global:thm:dimension` (line 1185) | Continuum many independent classes over the plane, and the exact dimension |
| Proposition | `global:prop:fullH1` (line 1210) | The full additive sheaf over the plane is already obstructed in cyclic rank |
| Proposition | `global:prop:Cartierexample` (line 1234) | A plane divisor with trivial ordinary reduction but no global equation |
| Lemma | `global:lem:compactsupport` (line 1348) | Compact support uniformity |
| Lemma | `global:lem:operatorneumann` (line 1364) | Neumann inverse, operator form |
| Proposition | `global:prop:dolbeault` (line 1388) | Dolbeault resolution over a compact base |
| Theorem | `global:thm:comparison` (line 1408) | Compact cohomology comparison |
| Lemma | `global:lem:unitsX` (line 1434) | Unit decomposition over a compact base |
| Theorem | `global:thm:piccompact` (line 1453) | Exact Picard classification over a compact base |
| Proposition | `global:prop:normalform` (line 1529) | Positive Dolbeault normal form |
| Theorem | `global:thm:finitecoh` (line 1567) | Finite cohomology and explicit representatives |
| Corollary | `global:cor:RRcompact` (line 1613) | Riemann--Roch in the zero-valuation sector |
| Proposition | `global:prop:degreezero` (line 1626) | Degree-zero deformations of the trivial bundle |
| Corollary | `global:cor:baseext` (line 1639) | Base extension does not remove an obstruction |
| Theorem | `global:thm:meromorphic` (line 1658) | Exact meromorphic-section criterion |
| Corollary | `global:cor:divseq` (line 1676) | The divisor-class sequence |
| Lemma | `global:lem:lognewton` (line 1731) | Logarithmic principal-part identity |
| Proposition | `global:prop:abelresidue` (line 1762) | Well-definedness and a residue formula |
| Theorem | `global:thm:abelcompact` (line 1786) | Support-controlled Abel criterion |
| Lemma | `global:lem:truncatedpic` (line 1892) | Truncated Picard classification |
| Lemma | `global:lem:coefficientlimit` (line 1922) | Inverse limit of the coefficient truncations |
| Theorem | `global:thm:adic` (line 1935) | Exact one-scale Picard comparison |
| Corollary | `global:cor:setcutoffs` (line 1972) | A set-indexed detection obstruction |

### nonabelian-support

Source: [surcomplex/nonabelian-support/article.tex](surcomplex/nonabelian-support/article.tex).

All statements in this newly indexed report remain **pending**. Criterion P
uses normalized polar-factor support, whereas Criterion M uses raw monodromy
support; the two predicates must not be identified.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `nab:lem:neumann` (line 631) | Neumann support calculus; classical input |
| Lemma | `nab:lem:inverse` (line 667) | Positive inversion and formal functions |
| Lemma | `nab:lem:finiteclosure` (line 698) | Finite decomposition inside the generated monoid |
| Lemma | `nab:lem:laurent` (line 739) | The ordinary splitting algebras |
| Lemma | `nab:lem:mlplane` (line 763) | Isolated singular parts on the plane |
| Lemma | `nab:lem:mlsurface` (line 788) | Open-surface version |
| Lemma | `nab:lem:free` (line 815) | Free based meridians |
| Lemma | `nab:lem:period` (line 850) | A linear period right inverse |
| Theorem | `nab:thm:local` (line 910) | Local normalized factorization |
| Proposition | `nab:prop:rightgauge` (line 946) | Right-gauge invariance |
| Corollary | `nab:cor:unitriangular` (line 967) | Unitriangular factors |
| Theorem | `nab:thm:frobenius` (line 1019) | A common-disk positive Frobenius factorization |
| Theorem | `nab:thm:criterion` (line 1103) | Exact nonabelian Cousin criterion: Criterion P |
| Proposition | `nab:prop:torsor` (line 1194) | Right torsor of splittings |
| Corollary | `nab:cor:localgauges` (line 1218) | Removal of arbitrarily supported regular data |
| Corollary | `nab:cor:coordinates` (line 1233) | Coordinate independence of admissibility |
| Corollary | `nab:cor:extension` (line 1251) | Absoluteness under ordered extension |
| Proposition | `nab:prop:rankone` (line 1273) | Recovery of the rank-one singular-support test |
| Proposition | `nab:prop:heisenberg` (line 1314) | Closed Heisenberg factorization |
| Theorem | `nab:thm:hidden` (line 1364) | Hidden rank-three obstruction |
| Proposition | `nab:prop:logdiag` (line 1436) | Logarithm diagnostic |
| Lemma | `nab:lem:chain` (line 1468) | Chain identity |
| Theorem | `nab:thm:depth` (line 1516) | Arbitrarily deep central support obstructions |
| Proposition | `nab:prop:integraltrivial` (line 1591) | For triviality, the reduced framing costs nothing |
| Corollary | `nab:cor:nontrivialbundles` (line 1611) | Nontrivial determinant-one integral bundles |
| Corollary | `nab:cor:bounded` (line 1627) | Exhaustion-invisible nontriviality |
| Theorem | `nab:thm:Stein` (line 1701) | Support-controlled Stein splitting |
| Theorem | `nab:thm:deformation` (line 1744) | Support-controlled deformation rigidity |
| Lemma | `nab:lem:groups` (line 1780) | Ordered-group alternative |
| Theorem | `nab:thm:dichotomy` (line 1796) | Universal positive rigidity and its failure |
| Theorem | `nab:thm:fundamental` (line 1935) | Fundamental matrix with a support certificate |
| Lemma | `nab:lem:triangular` (line 2010) | Triangular change of monodromy |
| Theorem | `nab:thm:RH` (line 2052) | Support-sensitive Riemann--Hilbert realization: Criterion M |
| Proposition | `nab:prop:intrinsic` (line 2146) | Independence of the meridian basis |
| Proposition | `nab:prop:conjugation` (line 2172) | Fixed conjugation and enlargement cannot repair support |
| Theorem | `nab:thm:gauge` (line 2209) | Framed classification with controlled support |
| Theorem | `nab:thm:entiregauge` (line 2245) | Entire extension of a logarithmic comparison gauge |
| Corollary | `nab:cor:slice` (line 2278) | A global normal slice for logarithmic connections |
| Corollary | `nab:cor:finite` (line 2305) | Unique positive residue matrices for finite data |
| Lemma | `nab:lem:det` (line 2336) | Determinants and positive connections |
| Theorem | `nab:thm:SL` (line 2351) | Traceless normalized realization |
| Proposition | `nab:prop:mixed` (line 2506) | The first nonabelian correction |
| Theorem | `nab:loc:thm:summary` (line 2674) | Summary of Part~III |
| Lemma | `nab:loc:lem:sheaf` (line 2831) | Sheaf property and preservation of support |
| Lemma | `nab:loc:lem:units` (line 2872) | Scalar units |
| Lemma | `nab:loc:lem:essential` (line 3004) | Essential protection |
| Theorem | `nab:loc:thm:obstruction` (line 3024) | Zero-annihilator descent obstruction |
| Corollary | `nab:loc:cor:annihilator` (line 3078) | A free cyclic obstruction submodule |
| Theorem | `nab:loc:thm:bounded` (line 3172) | Finite-puncture trivialization |
| Theorem | `nab:loc:thm:sections` (line 3231) | All global sections |
| Corollary | `nab:loc:cor:stable` (line 3275) | No stable trivialization |
| Corollary | `nab:loc:cor:meromorphic` (line 3291) | No coefficientwise meromorphic frame |
| Corollary | `nab:loc:cor:intermediate` (line 3312) | Intermediate coefficient categories |
| Corollary | `nab:loc:cor:enlarge` (line 3329) | Absolute resistance under ordered enlargement |
| Theorem | `nab:loc:thm:hom` (line 3353) | Complete morphism formula |
| Corollary | `nab:loc:cor:endomorphisms` (line 3391) | Hom spaces, endomorphisms and automorphisms |
| Theorem | `nab:loc:thm:indecomposable` (line 3414) | Indecomposability |
| Corollary | `nab:loc:cor:category` (line 3445) | Fully faithful realization |
| Corollary | `nab:loc:cor:jordan-class` (line 3474) | Classification within one profile |
| Proposition | `nab:loc:prop:flag` (line 3495) | The canonical global-section flag |
| Theorem | `nab:loc:thm:classification` (line 3524) | Integral equality versus localized translation |
| Corollary | `nab:loc:cor:class-enlarge` (line 3630) | Group enlargement creates no new profile identifications |
| Corollary | `nab:loc:cor:no-extra` (line 3645) | No additional identifications from meromorphic coefficients |
| Theorem | `nab:loc:thm:dichotomy` (line 3706) | Universal rigidity versus resistant examples |
| Theorem | `nab:loc:thm:continuum` (line 3764) | Cardinality lower bound in every noncyclic group |
| Theorem | `nab:loc:thm:tensor` (line 3835) | Tensor decomposition |
| Lemma | `nab:loc:lem:tensor` (line 3860) | The Jordan tensor rule |
| Proposition | `nab:loc:prop:poles` (line 3921) | Pole data are removable in the meromorphic category |
| Corollary | `nab:loc:cor:polestrivial` (line 3962) | Pole-data bundles die over $\MM$ |
| Proposition | `nab:loc:prop:essential-family` (line 4068) | Replacing the ordinary exponential |
| Proposition | `nab:prop:dependence` (line 4139) | Finite exponent dependence |
| Proposition | `nab:prop:basechange` (line 4173) | Compatibility with enlargement of the workspace |
| Proposition | `nab:prop:discontinuous` (line 4203) | No continuous linear period right inverse |
| Theorem | `nab:loc:thm:undecidable` (line 4257) | Neither side is semidecidable |

### polynomial-algebra

Source: [surcomplex/polynomial-algebra/article.tex](surcomplex/polynomial-algebra/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `polynomial:prop:workspace` (line 377) | A workspace for every set of data |
| Lemma | `polynomial:lem:support` (line 476) | Hahn--Neumann support calculus |
| Theorem | `polynomial:thm:fta` (line 589) | Finite polynomial algebra over $K$ |
| Theorem | `polynomial:thm:crt` (line 651) | Finite Hermite interpolation and CRT |
| Proposition | `polynomial:prop:rootbounds` (line 729) | Cauchy bounds and a radial bound |
| Theorem | `polynomial:thm:gausslucas` (line 766) | Surcomplex Gauss--Lucas |
| Proposition | `polynomial:prop:weighted` (line 795) | Weighted incomplete polynomials, and a converse |
| Theorem | `polynomial:thm:jensen` (line 821) | Surcomplex Jensen disk theorem |
| Lemma | `polynomial:lem:compression` (line 867) | Differentiating compression |
| Lemma | `polynomial:lem:schur` (line 878) | Finite-dimensional Schur inequality |
| Theorem | `polynomial:thm:schoenberg` (line 897) | Sharp surcomplex Schoenberg inequality |
| Theorem | `polynomial:thm:orderrouche` (line 972) | Rouch\'e on an order-modulus circle |
| Corollary | `polynomial:cor:pellet` (line 1002) | Monomial dominance |
| Theorem | `polynomial:thm:hermite` (line 1053) | Hermite's signature criterion over surreal real closed fields |
| Theorem | `polynomial:thm:pseudozeros` (line 1118) | Exact uncertainty root sets in two geometries |
| Lemma | `polynomial:lem:gaussvaluation` (line 1206) | Multiplicativity |
| Theorem | `polynomial:thm:initialroots` (line 1229) | Initial polynomial and all residue-direction root counts |
| Corollary | `polynomial:cor:valrouche` (line 1285) | Valuation Rouch\'e: preservation of the whole initial polynomial |
| Theorem | `polynomial:thm:newton` (line 1330) | Newton's root-valuation rule |
| Theorem | `polynomial:thm:imageballs` (line 1440) | Exact image and fiber degree |
| Corollary | `polynomial:cor:normalization` (line 1482) | Affine normalization of a finite polynomial problem |
| Theorem | `polynomial:thm:finitemap` (line 1515) | A polynomial is a finite flat map of its degree |
| Theorem | `polynomial:thm:branchvalues` (line 1539) | Branch-value polynomial |
| Proposition | `polynomial:prop:ramification` (line 1567) | Finite and infinite ramification |
| Corollary | `polynomial:cor:polynomialmaps` (line 1588) | Surjectivity and polynomial injections |
| Lemma | `polynomial:lem:initialderivative` (line 1608) | The derivative of an initial polynomial |
| Theorem | `polynomial:thm:criticalballs` (line 1631) | Exact critical-point conservation in occupied balls |
| Corollary | `polynomial:cor:ramificationball` (line 1663) | Ramification count on an arbitrary mapping ball |
| Corollary | `polynomial:cor:nearest` (line 1691) | Valuative Gauss--Lucas and nearest neighbours |
| Theorem | `polynomial:thm:branch` (line 1717) | Critical residue directions inside a cluster |
| Corollary | `polynomial:cor:tree` (line 1779) | Critical allocation by the root tree |
| Proposition | `polynomial:prop:clusterdisc` (line 1846) | Discriminant as a finite level sum |
| Proposition | `polynomial:prop:disctree` (line 1868) | Discriminant as a sum over the root tree |
| Theorem | `polynomial:thm:hensel` (line 1920) | Support-controlled coprime Hensel factorization |
| Corollary | `polynomial:cor:simpleroot` (line 1973) | Simple-root lifting and the first correction |
| Corollary | `polynomial:cor:clusterfactor` (line 1994) | Canonical standard-part cluster factors |
| Theorem | `polynomial:thm:parameterhensel` (line 2032) | Parameter factor lifting without repeated shrinking |
| Theorem | `polynomial:thm:holder` (line 2114) | Optimal valuation-H\"older root matching |
| Corollary | `polynomial:cor:derivativeholder` (line 2165) | Simultaneous stability for derivatives |
| Theorem | `polynomial:thm:stability` (line 2215) | Exact matching, full cluster stability, and a second-order Newton error |
| Corollary | `polynomial:cor:discprecision` (line 2354) | Discriminant precision protects all clusters |
| Corollary | `polynomial:cor:treestability` (line 2434) | Preservation of the tree and of its critical directions |
| Theorem | `polynomial:thm:residuepairing` (line 2510) | Universal residue pairing and explicit dual basis |
| Theorem | `polynomial:thm:trace` (line 2570) | Universal trace identity |
| Proposition | `polynomial:prop:localresidues` (line 2641) | Finite residue formula at multiple roots |
| Proposition | `polynomial:prop:tracenormroots` (line 2682) | Field-level traces and norms, including collisions |
| Theorem | `polynomial:thm:discriminant` (line 2707) | Discriminant and trace-pairing degeneration |
| Lemma | `polynomial:lem:zariski` (line 2793) | Zariski's lemma in the needed form |
| Theorem | `polynomial:thm:nullstellensatz` (line 2821) | Surcomplex Nullstellensatz |
| Proposition | `polynomial:prop:finitealgebra` (line 2886) | Finite fibers and local lengths |
| Theorem | `polynomial:thm:globalfree` (line 2975) | Global finite-free normal forms |
| Corollary | `polynomial:cor:globalbezout` (line 3027) | A global B\'ezout count, including infinite-scale roots |
| Theorem | `polynomial:thm:multiperfect` (line 3086) | A coefficient-independent perfect pairing |
| Theorem | `polynomial:thm:jacobian` (line 3127) | B\'ezoutian kernel and Jacobian duality |
| Corollary | `polynomial:cor:eulerjacobi` (line 3182) | Simple-root weights and Euler--Jacobi vanishing |
| Theorem | `polynomial:thm:polyparameters` (line 3226) | Global polynomial families on one ordinary parameter domain |
| Theorem | `polynomial:thm:analyticcomparison` (line 3268) | Polynomial identification of the Jacobian trace element |

### rank-one-berkovich

Source: [surcomplex/rank-one-berkovich/article.tex](surcomplex/rank-one-berkovich/article.tex).

All statements in this newly indexed report remain **pending**.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `prop:spherical` (line 267) | Untitled |
| Proposition | `prop:topologies` (line 313) | Untitled |
| Theorem | `thm:series` (line 341) | Untitled |
| Proposition | `prop:rankobstruction` (line 376) | Untitled |
| Proposition | `prop:banach` (line 455) | Untitled |
| Proposition | `prop:supnorm` (line 477) | Untitled |
| Theorem | `thm:chain` (line 546) | Untitled |
| Corollary | `cor:rescale` (line 626) | Untitled |
| Lemma | `lem:polydivision` (line 669) | Untitled |
| Theorem | `thm:preparation` (line 692) | One-variable Weierstrass division and preparation |
| Corollary | `cor:units` (line 742) | Untitled |
| Corollary | `cor:finitequotient` (line 758) | Untitled |
| Theorem | `thm:rootcounts` (line 814) | Untitled |
| Corollary | `cor:rouche` (line 845) | Valuation Rouch\'e theorem |
| Lemma | `lem:hensel` (line 861) | Unit-derivative Hensel lifting |
| Proposition | `prop:compact` (line 903) | Untitled |
| Corollary | `cor:types` (line 945) | Untitled |
| Proposition | `prop:slopes` (line 1052) | Untitled |
| Theorem | `thm:jensen` (line 1088) | Valuation Jensen formula |
| Proposition | `prop:primitive` (line 1124) | Untitled |
| Proposition | `prop:ode` (line 1164) | Untitled |
| Theorem | `thm:annulusderham` (line 1231) | Untitled |
| Proposition | `prop:residuepullback` (line 1260) | Untitled |
| Proposition | `prop:annuluscontract` (line 1295) | Untitled |
| Theorem | `thm:liouville` (line 1398) | Growth and zero-free rigidity |
| Theorem | `thm:canonicalproduct` (line 1427) | Untitled |
| Theorem | `thm:thetazeros` (line 1555) | All zeros and their first terms |
| Corollary | `cor:thetaresidue` (line 1653) | Untitled |

### spectral-theory

Source: [surcomplex/spectral-theory/article.tex](surcomplex/spectral-theory/article.tex).

All statements in this newly indexed report remain **pending**.

The expansion adds 29 pending obligations for descent without divisible
exponents, determinantal radical extensions and primitive trace generators.
Its dependency chain includes finite Hermitian spectral algebra, strong
support-controlled splitting and the stated Kummer-theoretic hypotheses;
the constructed closedness of divisible Hahn fields does not discharge the
nondivisible descent claims.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `prop:localization` (line 467) | Finite-data localization |
| Proposition | `spec:prop:exactlocalization` (line 493) | Exact-support localization |
| Lemma | `lem:CS` (line 538) | Cauchy--Schwarz and orthogonal decomposition |
| Theorem | `thm:spectral` (line 588) | Hermitian spectral theorem |
| Proposition | `prop:normal` (line 611) | Schur form and normal matrices |
| Proposition | `prop:positive` (line 647) | Positive square root and inertia |
| Theorem | `thm:svd` (line 680) | Singular value decomposition |
| Theorem | `thm:minmax` (line 789) | Variational principles |
| Theorem | `thm:weyl` (line 844) | Ordered Lipschitz bounds |
| Theorem | `thm:HW` (line 864) | A Frobenius eigenvalue bound |
| Theorem | `thm:leastsquares` (line 916) | Least squares with an attained minimum |
| Theorem | `thm:EY` (line 949) | Eckart--Young bounds over $F$ |
| Lemma | `lem:valnorm` (line 1014) | Valuation of a Euclidean norm |
| Lemma | `lem:unitaryintegral` (line 1038) | Unitary matrices preserve the integral lattice |
| Lemma | `lem:DeltaInvariant` (line 1071) | Integral row and column invariance |
| Theorem | `thm:scales` (line 1085) | Singular scales are determinantal scales |
| Theorem | `thm:gram` (line 1160) | Positive Cauchy--Binet identity |
| Theorem | `thm:residual` (line 1219) | Residual polynomial for a singular-scale block |
| Corollary | `spec:cor:gramscales` (line 1275) | Even determinantal scales of Gram matrices |
| Lemma | `spec:lem:words` (line 1351) | Ordered words |
| Lemma | `spec:lem:neumann` (line 1371) | Positive support monoids |
| Lemma | `spec:lem:evaluate` (line 1390) | Hahn evaluation |
| Corollary | `spec:cor:unitroots` (line 1419) | Exponent-preserving inverses and unit roots |
| Lemma | `spec:lem:lipschitz` (line 1432) | Formal maps are valuation nonexpanding |
| Lemma | `spec:lem:normroot` (line 1446) | Norms exist without real closedness |
| Theorem | `spec:thm:split` (line 1485) | Separated-block lifting |
| Proposition | `spec:prop:localstability` (line 1574) | Local valuation estimate |
| Theorem | `spec:thm:hermitian` (line 1606) | Hermitian Hahn spectral theorem |
| Corollary | `spec:cor:tree` (line 1654) | The splitting tree is finite |
| Corollary | `spec:cor:normal` (line 1697) | Normal spectral descent |
| Lemma | `spec:lem:commutant` (line 1715) | A finite-dimensional commutant fact |
| Theorem | `spec:thm:simultaneous` (line 1725) | Finite-witness simultaneous diagonalization |
| Theorem | `spec:thm:svd` (line 1762) | SVD over a nondivisible Hahn field |
| Corollary | `spec:cor:gramroot` (line 1784) | Gram square roots and polar decomposition |
| Proposition | `spec:prop:transport` (line 1849) | Order-preserving transport |
| Lemma | `spec:lem:scalarroot` (line 1920) | The scalar root formula |
| Lemma | `spec:lem:finiteindex` (line 1939) | Finite-index Hahn extensions |
| Theorem | `spec:thm:rootfield` (line 1981) | Principal-root field |
| Theorem | `spec:thm:ramification` (line 2037) | Determinantal ramification law |
| Corollary | `spec:cor:gramcriterion` (line 2086) | Exact Gram-factorization criterion |
| Corollary | `spec:cor:rationalpower` (line 2100) | Rational powers |
| Lemma | `spec:lem:positivetrace` (line 2193) | Positive radical sums retain every generator |
| Theorem | `spec:thm:primitivetrace` (line 2225) | Primitive trace |
| Corollary | `spec:cor:realtrace` (line 2250) | The corresponding real field |
| Corollary | `spec:cor:joint` (line 2300) | Joint ramification and a joint primitive element |
| Corollary | `spec:cor:surcomplex` (line 2325) | Exact-support surcomplex spectral calculus |
| Lemma | `spec:hank:lem:intermediate` (line 2451) | Intermediate fields of half-scale extensions |
| Corollary | `spec:hank:cor:adjoin` (line 2491) | Adjoining finitely many positive square roots |
| Lemma | `spec:hank:lem:hensel` (line 2512) | Coprime Hensel lifting over $F_\Gamma$ |
| Proposition | `spec:hank:prop:hermite` (line 2645) | Classical trace-form and subdiscriminant identities |
| Theorem | `spec:hank:thm:field` (line 2709) | Subdiscriminants give the entire splitting field |
| Corollary | `spec:hank:cor:split` (line 2764) | A root-free splitting criterion |
| Corollary | `spec:hank:cor:primitive` (line 2770) | A coefficient-defined primitive element |
| Lemma | `spec:hank:lem:graded` (line 2820) | Square-class multiplicities are invariant under congruence |
| Theorem | `spec:hank:thm:profile` (line 2871) | Factor-count and character-profile theorem |
| Corollary | `spec:hank:cor:irreducible` (line 2924) | Irreducibility without factorization |
| Corollary | `spec:hank:cor:character` (line 2943) | The root permutation character |
| Theorem | `spec:hank:thm:realizable` (line 2970) | Realizability of the complete profile |
| Theorem | `spec:hank:thm:basechange` (line 3009) | Exact base-change formulas |
| Proposition | `spec:hank:prop:invariance` (line 3043) | Additivity and affine invariance |
| Theorem | `spec:hank:thm:precision` (line 3071) | Stability of the complete profile |
| Corollary | `spec:hank:cor:coeffprecision` (line 3096) | A sufficient coefficient precision for integral inputs |
| Theorem | `spec:hank:thm:pencil` (line 3144) | Exact eigenvalue fields of definite pencils |
| Theorem | `spec:hank:thm:realization` (line 3180) | A positive definite realization in dimension $2r$ |
| Proposition | `spec:hank:prop:single` (line 3217) | One primitive eigenvalue costs $2^r$ dimensions |
| Corollary | `cor:stRank` (line 3543) | Rank after reduction |
| Theorem | `thm:filtration` (line 3576) | Filtration dimensions |
| Proposition | `prop:elimination` (line 3634) | Exact scale elimination |
| Theorem | `thm:distance` (line 3772) | Distance to singularity |
| Theorem | `thm:inversepert` (line 3806) | Inverse and linear-system perturbation |
| Theorem | `thm:precision` (line 3849) | Preserving visible singular data |
| Proposition | `prop:pseudo` (line 3905) | Exact perturbation interpretation |
| Theorem | `thm:subspace` (line 3958) | A separated-subspace bound |
| Corollary | `cor:clustergap` (line 4004) | Using an unperturbed cluster gap |
| Proposition | `prop:effective` (line 4072) | Exact effective matrix |
| Theorem | `thm:series` (line 4199) | Matrix inverse and square-root series |
| Proposition | Line 4300 (unlabeled) | Ordinary data and infinitesimal regularization |

### trigonometry

Source: [surcomplex/trigonometry/article.tex](surcomplex/trigonometry/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `trigonometry:lem:support` (line 350) | Hahn--Neumann support calculus |
| Proposition | `trigonometry:prop:topology` (line 400) | Degeneracy of fine convergence |
| Proposition | `trigonometry:prop:lift` (line 432) | Local calculus and one-variable sign lifting |
| Lemma | `trigonometry:lem:leading` (line 461) | Leading-term test for a lifted germ |
| Theorem | `trigonometry:thm:identities` (line 501) | Elementary trigonometry on finite surreal angles |
| Proposition | `trigonometry:prop:order` (line 541) | Signs and monotonicity |
| Proposition | `trigonometry:prop:leading` (line 566) | Exact infinitesimal leading orders |
| Proposition | `trigonometry:prop:normalization` (line 589) | Normalization of the finite trigonometric pair |
| Proposition | `trigonometry:prop:rotation` (line 639) | Algebraic angle addition and rotations |
| Theorem | `trigonometry:thm:polar` (line 665) | Polar decomposition and the angle group |
| Corollary | `trigonometry:cor:representatives` (line 698) | Representatives, roots, and torsion |
| Theorem | `trigonometry:thm:cayley` (line 744) | Projective half-angle parametrization of every surreal direction |
| Theorem | `trigonometry:thm:inverse` (line 783) | Inverse tangent, sine, and cosine |
| Proposition | `trigonometry:prop:acosendpoint` (line 853) | Endpoint ramification of inverse cosine |
| Theorem | `trigonometry:thm:metric` (line 881) | Angular and chordal comparison |
| Corollary | `trigonometry:cor:phaseisometry` (line 913) | Local valuation isometry of phase and rotation displacement |
| Corollary | `trigonometry:cor:directionstability` (line 937) | Stability of direction under a relative perturbation |
| Theorem | `trigonometry:thm:anglesum` (line 970) | Euclidean angle sum over the surreal field |
| Theorem | `trigonometry:thm:trianglelaws` (line 992) | Triangle laws |
| Corollary | `trigonometry:cor:right` (line 1020) | Right triangles and the full range of slopes |
| Theorem | `trigonometry:thm:sss` (line 1031) | Existence, congruence, and similarity |
| Theorem | `trigonometry:thm:heron` (line 1080) | Heron, half-angle, incircle and bisector formulas |
| Theorem | `trigonometry:thm:euler` (line 1119) | Euler's incentre--circumcentre identity |
| Corollary | `trigonometry:cor:areabound` (line 1141) | A scale-independent area inequality |
| Theorem | `trigonometry:thm:cevian` (line 1156) | Sine ratios for a cevian |
| Theorem | `trigonometry:thm:ceva` (line 1173) | Trigonometric Ceva |
| Proposition | `trigonometry:prop:inscribed` (line 1212) | Inscribed-angle theorem |
| Theorem | `trigonometry:thm:ptolemy` (line 1225) | Ptolemy inequality and its cyclic equality case |
| Corollary | `trigonometry:cor:polygon` (line 1254) | Finite regular polygons at surreal scale |
| Theorem | `trigonometry:thm:valuationtriangle` (line 1300) | Valuation form of the triangle laws |
| Theorem | `trigonometry:thm:defect` (line 1339) | A quadratic defect formula |
| Theorem | `trigonometry:thm:flat` (line 1371) | Quadratic slack and reciprocal circumradius in normalized coordinates |
| Theorem | `trigonometry:thm:flatrelative` (line 1409) | Exact gap identity and the relative flatness threshold |
| Theorem | `trigonometry:thm:amplitude` (line 1546) | Amplitude--phase reduction and intersection count |
| Theorem | `trigonometry:thm:tangency` (line 1582) | Tangency, angular splitting, and loss of valuation |
| Theorem | `trigonometry:thm:fold` (line 1624) | The cosine fold |
| Theorem | `trigonometry:thm:residuepairing` (line 1666) | A collision-stable residue pairing |
| Lemma | `trigonometry:lem:hensel` (line 1764) | A simple residue root of a polynomial |
| Theorem | `trigonometry:thm:stability` (line 1783) | Sharp angular root-stability bound |
| Proposition | `trigonometry:prop:sharp` (line 1838) | The threshold and both exponents are sharp |
| Theorem | `trigonometry:thm:conditioned` (line 1862) | Conditioned inversion of cosine |
| Theorem | `trigonometry:thm:stripexp` (line 1947) | Canonical strip exponential |
| Theorem | `trigonometry:thm:striptrig` (line 1978) | Complex-variable identities and zero sets |
| Theorem | `trigonometry:thm:sinefibers` (line 2005) | Surjectivity and complete fibres of strip sine |
| Corollary | `trigonometry:cor:sineinverse` (line 2030) | Explicit inverse branches |
| Theorem | `trigonometry:thm:polyroots` (line 2067) | Algebraization and the $2n$ root bound |
| Corollary | `trigonometry:cor:chebyshev` (line 2099) | Chebyshev and extremum equations |
| Theorem | `trigonometry:thm:cluster` (line 2129) | Exact cluster multiplicity and coefficient support |
| Theorem | `trigonometry:thm:fourier` (line 2206) | Finite Fourier inversion, sampling, and Parseval |
| Theorem | `trigonometry:thm:parseval` (line 2264) | Finite Fourier identities over $\SC$ |
| Lemma | `trigonometry:lem:twosquares` (line 2320) | Nonnegative polynomials over a real closed field |
| Theorem | `trigonometry:thm:fejer` (line 2334) | Surcomplex Fej\'er--Riesz theorem |
| Corollary | `trigonometry:cor:coeffbounds` (line 2396) | Fourier coefficient bounds from positivity |
| Theorem | `trigonometry:thm:spherical` (line 2464) | Spherical cosine and sine laws |
| Proposition | `trigonometry:prop:diskmetric` (line 2516) | Disk invariance and metric properties |
| Theorem | `trigonometry:thm:hyperbolic` (line 2546) | Hyperbolic triangle laws over $\No$ |
| Theorem | `trigonometry:thm:arcs` (line 2608) | Circle length and sector area at every radius |
| Proposition | `trigonometry:prop:perimeters` (line 2635) | Failure of fine convergence of inscribed perimeters |
| Theorem | `trigonometry:thm:globalexp` (line 2712) | Canonical global exponential and its period class |
| Corollary | `trigonometry:cor:globalzeros` (line 2751) | Zero classes and periods |
| Theorem | `trigonometry:thm:characters` (line 2772) | All extensions of the finite phase |
| Theorem | `trigonometry:thm:infiniteperiods` (line 2820) | Infinite periods are unavoidable |
| Theorem | `trigonometry:thm:infinitefrequency` (line 2855) | No coherent infinite-frequency bounded sine |
| Theorem | `trigonometry:thm:allscale` (line 2880) | Why all-scale coherence forces a polynomial |

### surquaternions

Source: [surquaternions/surquaternions/article.tex](surquaternions/surquaternions/article.tex).

All statements in this newly indexed report remain **pending**. Quaternion
multiplication, conjugation and leading coefficients retain their stated
noncommutative order; scalar commutative proofs do not transfer implicitly.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `squat:thm:localization` (line 333) | Set localization |
| Proposition | `squat:prop:assoc` (line 570) | Associativity and change of scalars |
| Theorem | `squat:thm:division` (line 584) | Hamilton algebra over an ordered field |
| Proposition | `squat:prop:center` (line 609) | Center, commutators, and the absence of a ring order |
| Proposition | `squat:prop:norm` (line 636) | Euclidean identities without completeness |
| Theorem | `squat:thm:conjugacy` (line 696) | Slice decomposition, centralizers, conjugacy |
| Proposition | `squat:prop:sqrt` (line 726) | Explicit square roots |
| Proposition | `squat:prop:matrix` (line 754) | Matrix realization |
| Theorem | `squat:thm:rotations` (line 793) | Rotations, spin, and inner automorphisms |
| Proposition | `squat:prop:charts` (line 861) | Cayley and stereographic presentations of one chart |
| Lemma | `squat:lem:twisted` (line 951) | Twisted product and left division |
| Lemma | `squat:lem:sphere-remainder` (line 989) | Remainder on a sphere |
| Theorem | `squat:thm:polynomialzeros` (line 1025) | Complete zero-class criterion |
| Theorem | `squat:thm:fta` (line 1040) | Constructive fundamental theorem and factorization |
| Proposition | `squat:prop:rootcount` (line 1069) | Conservation of class multiplicity |
| Theorem | `squat:thm:normal` (line 1127) | Normal form, multiplication, localization |
| Theorem | `squat:thm:valuation` (line 1175) | Exact valuation, leading coefficients, and residue |
| Proposition | `squat:prop:neumann` (line 1232) | Exact geometric inverse and error certificate |
| Lemma | `squat:lem:neumann` (line 1280) | Positive-support (Neumann) lemma, all lengths |
| Theorem | `squat:thm:discrete` (line 1331) | Set discreteness and the failure of sequential completion |
| Theorem | `squat:thm:principal-log` (line 1412) | Local exponential--logarithm equivalence |
| Proposition | `squat:prop:bch` (line 1449) | Baker--Campbell--Hausdorff at positive valuation |
| Proposition | `squat:prop:adjoint` (line 1504) | Adjoint series at infinite arguments |
| Theorem | `squat:thm:rotation-log` (line 1521) | Logarithms of infinitesimal rotations |
| Theorem | `squat:thm:graded` (line 1536) | Associated graded rotation algebra |
| Proposition | `squat:prop:finiteangles` (line 1579) | Every direction has a finite angle; the finite phase theorem |
| Theorem | `squat:thm:polar` (line 1602) | Polar representation at arbitrary surreal radius |
| Theorem | `squat:thm:polarlog` (line 1653) | Polar logarithms and arbitrary-scale roots |
| Theorem | `squat:thm:globalexp` (line 1751) | Properties of the global radial exponential |
| Theorem | `squat:thm:logfibres` (line 1793) | Complete logarithm fibres |
| Theorem | `squat:thm:exp-derivative` (line 1857) | Radial derivative and critical spheres at infinite radius |
| Theorem | `squat:thm:derivations` (line 1926) | Derivation decomposition |
| Corollary | `squat:cor:bmconstants` (line 1994) | Constants, surjectivity, antiderivatives |
| Proposition | `squat:prop:angular` (line 2031) | Angular velocity identity |
| Lemma | `squat:lem:small` (line 2052) | Finite inputs have infinitesimal derivatives |
| Theorem | `squat:thm:nooscillation` (line 2061) | No constant-frequency quaternionic oscillation |
| Corollary | `squat:cor:nochain` (line 2082) | No global commuting chain rule |
| Theorem | `squat:thm:spectral` (line 2163) | Hermitian spectral theorem over $\HF$ |
| Theorem | `squat:thm:projector` (line 2256) | Spectral-projector estimate at arbitrary surreal gap scale |
| Proposition | `squat:prop:evaluation` (line 2373) | Uniform-support evaluation |
| Proposition | `squat:prop:representation` (line 2427) | Slice representation, Cauchy--Riemann, twisted product |
| Theorem | `squat:thm:representation` (line 2517) | Representation formula and coherent identity principle |
| Theorem | `squat:thm:cauchy-general` (line 2588) | Common-domain Cauchy formula at arbitrary slice direction |
| Theorem | `squat:thm:cauchy-slice` (line 2632) | Coefficientwise Cauchy formula on a fixed slice |
| Theorem | `squat:thm:fueter` (line 2701) | Fueter transfer: polynomials and coherent families |
| Theorem | `squat:thm:lifting` (line 2773) | Support-controlled implicit lifting |
| Proposition | `squat:prop:sylvester` (line 2840) | Square-root linearization and condition numbers |
| Theorem | `squat:thm:conditioned` (line 2893) | A sufficient conditioned square-root threshold |

### broadcast-sum-of-surreal-sequences

Source: [surreal/broadcast-sum-of-surreal-sequences/article.tex](surreal/broadcast-sum-of-surreal-sequences/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:terminal` (line 316) | Positions with no moves |
| Lemma | `lem:rank-monotone` (line 368) | Monotonicity of the auxiliary rank |
| Theorem | `thm:rank` (line 386) | Well-foundedness and a birthday bound |
| Lemma | `lem:commute` (line 438) | Commutation |
| Lemma | `lem:legalize` (line 456) | A nonidentity action can be legalized |
| Lemma | `lem:survive` (line 472) | The earlier witness survives |
| Theorem | `thm:number` (line 486) | Every broadcast game is a number |
| Proposition | `prop:basic` (line 533) | Relabelling, zeros, and negation |
| Theorem | `thm:finite-support` (line 550) | Finite-support agreement |
| Corollary | `cor:ordinal` (line 572) | Ordinal extension |
| Theorem | `thm:perturbation` (line 597) | Finite-short-perturbation bound |
| Corollary | `cor:cofinite` (line 655) | Untitled |
| Lemma | `lem:X-cuts` (line 682) | Untitled |
| Theorem | `thm:constants` (line 709) | Constant dyadic values and finite defects |
| Corollary | `cor:dyadic-tail` (line 770) | Cofinite dyadic leading scale |
| Lemma | `lem:left-family` (line 805) | Left options |
| Lemma | `lem:right-family` (line 832) | Right options |
| Theorem | `thm:finite-E` (line 854) | Untitled |
| Theorem | `thm:infinite-E` (line 873) | Untitled |
| Lemma | `lem:pure-power` (line 918) | Pure geometric tails |
| Corollary | `cor:nonmonotone` (line 932) | Failure of weak monotonicity |
| Corollary | `cor:scaling` (line 952) | Failure of finite-scaling compatibility |

### canonical-forms-need-not-be-subgraphs

Source: [surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex](surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:pentagon` (line 453) | A pentagon represents $1/2$ |
| Theorem | `thm:second-pentagon` (line 528) | A second pentagon of value $1/2$ |
| Lemma | `lem:cone` (line 642) | Convexity of a simplicity cone |
| Lemma | `lem:descent` (line 660) | Descent toward a prefix |
| Theorem | `thm:prefix-occurrence` (line 683) | Prefix occurrence |
| Lemma | `lem:canonical-prefix` (line 717) | The finite canonical prefix chain |
| Theorem | `thm:prefix-path` (line 772) | A path through every finite prefix |
| Lemma | `lem:one-sided` (line 805) | One-sided finite cuts have integer values |
| Theorem | `thm:minima` (line 819) | Exact graph minima |
| Corollary | `cor:acyclic` (line 864) | Untitled |
| Lemma | `lem:forest` (line 880) | Forest obstruction |
| Theorem | `thm:minimal-forms` (line 907) | The vertex-minimal forms |
| Corollary | `cor:edge-unique` (line 963) | Unique edge-minimizer |
| Lemma | `lem:quadrilateral` (line 1008) | Triangle-free forms on at most four vertices |
| Theorem | `thm:smallest` (line 1044) | Smallest size and rank of a counterexample |
| Proposition | `prop:rank-minimal` (line 1088) | A rank-minimal non-containing form |
| Lemma | `lem:zero-spine` (line 1184) | Untitled |
| Theorem | `thm:odd-cycle` (line 1201) | Odd-cycle family |
| Lemma | `lem:alternating-spine` (line 1250) | Untitled |
| Theorem | `thm:odd-cycle-two` (line 1264) | Second odd-cycle family |
| Theorem | `thm:even-cycle` (line 1307) | Even-cycle family |
| Proposition | `prop:allcycles` (line 1338) | All cycle lengths except four |
| Theorem | `thm:extremal` (line 1357) | Exact extremal function for $1/2$ |
| Theorem | `thm:high-girth` (line 1431) | Spaced-spine construction |
| Corollary | `cor:unbounded-girth` (line 1514) | Unbounded girth at every fixed value |
| Corollary | `cor:avoid-graph` (line 1528) | Avoiding every fixed cyclic graph |
| Proposition | `prop:fibonacci` (line 1544) | A Fibonacci bound on the unfolded leaves |
| Proposition | `prop:fibonacci-alt` (line 1581) | A denominator-sensitive bound, second proof |
| Lemma | `lem:markers` (line 1681) | Separated integer markers |
| Lemma | `lem:values` (line 1730) | Value preservation |
| Lemma | `lem:nocollapse` (line 1743) | No unintended identifications |
| Lemma | `lem:graphbounds` (line 1775) | Graph bounds |
| Theorem | `thm:sparse` (line 1804) | Planar high-girth representation theorem |
| Lemma | `lem:canonical-triangle` (line 1858) | A triangle in every noninteger canonical graph |
| Theorem | `thm:integer-classification` (line 1877) | Exactly the integers, unlabelled version |
| Theorem | `thm:classification-rooted` (line 1912) | Exactly the integers, rooted-colour version |
| Proposition | `prop:omega` (line 1979) | A limit-stage coherence obstruction |
| Proposition | `prop:omega-highgirth` (line 2049) | Exact high-girth forms of $\omega$ |
| Proposition | `prop:konig` (line 2088) | No transfinite form has finite outdegree everywhere |

### exponential-automorphism-rigidity

Source: [surreal/exponential-automorphism-rigidity/article.tex](surreal/exponential-automorphism-rigidity/article.tex).

All statements in this report remain **pending**. The elementary twisted
product and displacement lemmas can precede the valuation and exponential
results. Later claims retain a total increasing surjective ordered
exponential, a nontrivial convex valuation and any specified stabilization
hypotheses; the existing infinitesimal and finite Hahn exponential does not
supply that global structure. The September 22 source check confirmed the
correspondence with Question 5.4 in the pinned KKS v3 PDF, as recorded in the
report; this is separate from proving the Lean statements. The logarithmic-modulus
classification additionally retains the stated real-closedness hypothesis.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:intro` (line 157) | Main rigidity theorem |
| Lemma | `lem:bridge` (line 288) | The bridge |
| Lemma | `lem:bounded` (line 312) | Proper convex subgroups are bounded |
| Proposition | `prop:finite-log` (line 345) | Untitled |
| Lemma | `lem:amplify` (line 381) | Quantitative displacement amplification |
| Corollary | `cor:bounded-displacement` (line 416) | Bounded-displacement rigidity |
| Proposition | `prop:valued-amplification` (line 431) | Untitled |
| Theorem | `thm:sigma-derivation` (line 477) | No globally valuation-bounded nonzero $\sigma$-derivation |
| Proposition | `prop:sigma-witness` (line 519) | Ordered two-point witness |
| Theorem | `thm:cofinal` (line 566) | Cofinal value displacement |
| Corollary | `cor:faithful` (line 583) | Faithfulness |
| Corollary | `cor:embedding` (line 603) | Self-embedding version |
| Theorem | `thm:visible-scale` (line 631) | Rigidity from one visible exponential scale |
| Corollary | `cor:detector` (line 688) | Exponential detector |
| Theorem | `thm:coarsening` (line 727) | Coarsening rigidity |
| Corollary | `cor:unique-lift` (line 745) | At most one exponential lift |
| Proposition | `prop:probes` (line 760) | Two exponential probes |
| Theorem | `thm:no` (line 796) | No invisible surreal exponential automorphisms |
| Corollary | `cor:question54` (line 821) | Answer to Question 5.4 |
| Theorem | `thm:profile` (line 891) | Profile rigidity |
| Corollary | `cor:tail` (line 925) | Tail commutation suffices |
| Corollary | `cor:two-profiles` (line 941) | Comparing two automorphisms by profile |
| Theorem | `thm:motion` (line 972) | Multiplicative motion is cofinal |
| Theorem | `thm:defect` (line 1010) | Cofinal commutation defects |
| Corollary | `cor:approx` (line 1038) | No uniformly bounded approximate commutation |
| Proposition | `prop:single-layer` (line 1091) | Untitled |
| Theorem | `thm:bounded-layers` (line 1125) | Bounded-layer obstruction |
| Proposition | `prop:hahn-lift` (line 1163) | Canonical field lift |
| Theorem | `thm:dilation` (line 1206) | Rational dilations do not lift |
| Lemma | `lem:range` (line 1291) | Recovery of the real subfield |
| Theorem | `thm:L-classification` (line 1309) | Logarithmic-modulus classification |
| Lemma | `lem:wK` (line 1373) | Untitled |
| Theorem | `thm:complex-kernel` (line 1399) | Surcomplex valuation kernel |
| Corollary | `cor:surcomplex` (line 1424) | Surcomplex application |
| Lemma | `lem:derivation-amplify` (line 1448) | Untitled |
| Theorem | `thm:derivation` (line 1465) | No globally nonexpanding exponential derivation |
| Theorem | `thm:derivation-valued` (line 1505) | Unbounded valuation loss |
| Corollary | `cor:no-contraction` (line 1533) | Rescaling does not help |
| Proposition | `prop:substitution` (line 1603) | Untitled |
| Proposition | `prop:partial-exp` (line 1662) | Untitled |
| Proposition | `prop:additive-bounded` (line 1695) | Untitled |

### gamma-functions

Source: [surreal/gamma-functions/article.tex](surreal/gamma-functions/article.tex).

All statements in this report remain **pending**. Dependencies include the
actual normal-form and exponential constructions, restricted-analytic
transfer, strong Taylor–Stirling evaluation and the specified fine calculus;
scalar rigidity additionally uses the Berarducci–Mantova derivation. The
convexity classification concerns the stated monomialwise gauge family,
and the surcomplex phase results retain their finite-imaginary-part tube.
No uniqueness among arbitrary Gamma extensions is inferred.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:main` (line 199) | Sharp convexity and simultaneous invariance |
| Corollary | `cor:headline` (line 232) | Explicit strengthened nonuniqueness |
| Proposition | `prop:baseline-calculus` (line 444) | Well-definedness and local calculus |
| Lemma | `lem:formal-shift` (line 498) | Formal shift identity |
| Lemma | `lem:periodic` (line 532) | No nonconstant periodic inverse-power series |
| Proposition | `prop:gauss0` (line 541) | Exact Gauss identity for the baseline |
| Lemma | `lem:tangent-convex` (line 585) | Tangent support and convexity |
| Lemma | `lem:infinite-gaps` (line 614) | Infinite-argument tangent gaps |
| Lemma | `lem:mixed-gaps` (line 702) | Finite and mixed tangent gaps |
| Theorem | `thm:baseline-convex` (line 757) | Global strict log-convexity of the baseline |
| Lemma | `lem:gauge-identities` (line 785) | Gauge identities |
| Proposition | `prop:gauge-invariance` (line 808) | Identities shared by every gauge |
| Theorem | `thm:sufficiency` (line 838) | Convexity under the sharp bound |
| Theorem | `thm:necessity` (line 889) | Necessity of the finite coefficient bound |
| Corollary | `cor:sharp-region` (line 920) | The exact coefficient region |
| Proposition | `prop:flat-equivalence` (line 974) | Coefficient flatness equals function flatness |
| Theorem | `thm:independent` (line 1039) | Independent monomial parameters |
| Theorem | `thm:enveloping` (line 1095) | Enveloping inequalities are still non-unique |
| Theorem | `thm:complex-log` (line 1316) | Surcomplex logarithmic invariance |
| Lemma | `lem:phase` (line 1359) | Imaginary log-Gamma at infinite real part |
| Theorem | `thm:phase-domain` (line 1394) | Exact canonical finite-phase Gamma domain |
| Proposition | `prop:BM-baseline` (line 1473) | The baseline satisfies the scalar chain rule |
| Theorem | `thm:BM-flat` (line 1495) | Scalar compatibility removes flat local gauges |
| Theorem | `thm:BM-all` (line 1519) | Complete scalar rigidity inside the monomialwise family |
| Proposition | `prop:real-gauge` (line 1559) | A different real-valued gauge survives scalar compatibility |
| Theorem | `thm:abstract` (line 1601) | Scale-margin gauge principle |

### genetic-gaps-and-primitives

Source: [surreal/genetic-gaps-and-primitives/article.tex](surreal/genetic-gaps-and-primitives/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:q` (line 223) | A bounded sign-preserving rational function |
| Lemma | `lem:binary` (line 241) | A binary cut test |
| Theorem | `thm:evaluation` (line 267) | Exact evaluation |
| Proposition | `prop:genetic` (line 327) | Untitled |
| Lemma | `lem:translation` (line 393) | Invariance under finite translation |
| Theorem | `thm:zero` (line 406) | The kernel is not just the constants |
| Theorem | `thm:primitive` (line 432) | Counterexample to genetic primitive uniqueness |
| Corollary | Line 468 (unlabeled) | Failure of normalized global uniqueness |
| Theorem | `thm:sup` (line 492) | Counterexample to the entire-genetic sup conjecture |
| Theorem | `thm:general` (line 546) | General gap-indicator construction |
| Proposition | Line 609 (unlabeled) | Cofinality is the invariant |
| Theorem | `thm:auto` (line 638) | Untitled |
| Theorem | `thm:independent` (line 682) | Ordinal-indexed finite linear independence |
| Proposition | `prop:rational` (line 797) | Rational primitives remain unique |
| Proposition | `prop:field` (line 825) | Untitled |

### gonshor-laurent-birthdays

Source: [surreal/gonshor-laurent-birthdays/article.tex](surreal/gonshor-laurent-birthdays/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:main` (line 143) | Laurent-series restriction |
| Lemma | `lem:add` (line 260) | Untitled |
| Lemma | `lem:realproduct` (line 300) | Real scalar product bound |
| Lemma | `lem:prefix` (line 343) | Prefixes and countable unions |
| Lemma | `lem:block` (line 366) | Untitled |
| Theorem | `thm:ordinalpoly` (line 399) | Ordinal-exponent polynomials |
| Theorem | `thm:finiteformula` (line 471) | Finite Laurent formula |
| Corollary | `cor:split` (line 549) | Exact finite splitting |
| Lemma | `lem:bounded` (line 590) | Untitled |
| Lemma | `lem:degree` (line 626) | Untitled |
| Lemma | `lem:crossmono` (line 649) | Positive monomial times bounded part |
| Corollary | `cor:crosspoly` (line 699) | Untitled |
| Theorem | `thm:finiteproduct` (line 716) | Finite Laurent product theorem |
| Corollary | `cor:strict` (line 745) | Equality with a finite negative tail |
| Theorem | `thm:infinite` (line 796) | Infinite Laurent birthday formula |
| Lemma | `lem:jets` (line 846) | Finite-jet stabilization |
| Corollary | `cor:reciprocal` (line 952) | Untitled |
| Corollary | `cor:spectrum` (line 991) | Untitled |

### gonshor-product-birthdays

Source: [surreal/gonshor-product-birthdays/surreal_product_birthdays.tex](surreal/gonshor-product-birthdays/surreal_product_birthdays.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:degree-arithmetic` (line 261) | Untitled |
| Lemma | `lem:interval` (line 292) | Untitled |
| Proposition | `prop:closure` (line 341) | Untitled |
| Theorem | `thm:endpoint` (line 465) | Exact birthday |
| Corollary | `cor:support-sandwich` (line 591) | Untitled |
| Theorem | `thm:support-product` (line 613) | Sharp support bound |
| Proposition | `prop:infinite-gap` (line 644) | Strict degree gap |
| Lemma | `lem:dyadic-product` (line 683) | Dyadic factors |
| Lemma | `lem:scalar` (line 708) | A dyadic scalar cannot increase the leading birthday data |
| Theorem | `thm:main` (line 761) | Product birthdays on \(\A\) |
| Corollary | `cor:degree` (line 785) | Degree does not rise |
| Proposition | `prop:four` (line 821) | No full convolution is needed |
| Proposition | `prop:bounded` (line 996) | Untitled |
| Proposition | `prop:local` (line 1025) | Untitled |

### hahn-evaluation-at-omega

Source: [surreal/hahn-evaluation-at-omega/article.tex](surreal/hahn-evaluation-at-omega/article.tex).

The maintained report corrects `rem:incomparable`: restriction and unique
extension by coefficientwise differences identify unital ring and semiring
maps into a commutative ring. The witnesses give different direct proofs,
not logically incomparable homomorphism obstructions. The new extension
argument remains a separate formalization obligation.

The expanded `thm:exact`, including all four existence alternatives,
strong additivity, the literal evaluation formula and nonzero-input injectivity,
is proved above on the actual universe-indexed carrier. Uniqueness among
coefficient-fixing strongly additive maps and explicit leading data are also
proved. The permitted lower-universe index bound remains visible; no
uniqueness among arbitrary abstract homomorphisms is asserted. The new simple
algebraic extension/root correspondence and intrinsic Laurent-field geometric
convergence likewise remain separate obligations.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:witness` (line 315) | The formal square-root witness |
| Theorem | `thm:main` (line 351) | Negative answer to Problem 7.7 |
| Proposition | `prop:small` (line 384) | Untitled |
| Lemma | `lem:H` (line 503) | The nonnegative witness pair |
| Theorem | `thm:semiring` (line 539) | Nonnegative-coefficient obstruction |
| Lemma | `lem:unitsquare` (line 620) | Square roots of formal units |
| Lemma | `lem:unit-root` (line 641) | Square roots of units, general form |
| Theorem | `thm:necessary` (line 666) | Necessary infinitesimal condition |
| Proposition | `prop:kernel` (line 686) | The kernel dichotomy |
| Theorem | `thm:exact` (line 726) | Exactly which values of $x$ occur |
| Lemma | `lem:positivesquare` (line 885) | Every canonically positive element is a square |
| Theorem | `thm:orderforced` (line 905) | Order is algebraically forced |
| Theorem | `thm:reversal` (line 950) | Exponent-reversing isomorphism |
| Theorem | `thm:classification` (line 1018) | Complete existence criterion for pure monomial data |
| Proposition | `prop:rational` (line 1141) | Untitled |
| Proposition | `prop:algebraic` (line 1215) | Criterion for a simple algebraic extension |
| Lemma | `lem:subseq` (line 1464) | Nondecreasing subsequences |
| Lemma | `lem:higman` (line 1492) | Higman's lemma, well-ordered alphabet case |
| Lemma | `lem:neumann` (line 1531) | Positive-support summability |
| Corollary | `cor:convolution` (line 1576) | Untitled |
| Lemma | `lem:two-supports` (line 1605) | Two supports, elementarily |
| Corollary | `cor:substitution` (line 1627) | Substitution into a positive-support series |
| Proposition | `prop:field` (line 1657) | Untitled |


### computable-surreals

Source: [foundations-and-computation/computable-surreals/article.tex](foundations-and-computation/computable-surreals/article.tex).

The maintained report corrects `lem:geom` by filtering candidate covers to
`[0,B)`; valid raw input names can contain negative zero candidates. The
statement `prop:topology` now distinguishes full-class set indices from
lower-universe-small indices. The finite cover regression and working
verification runner do not discharge these mathematical proof obligations.

All 56 statements in this report remain **pending**. The three representations
must stay distinct: hereditary computable Conway cuts, effective rational
left-finite series with finite candidate covers, and computable Puiseux series
with one bounded denominator per series. Numerical closure and lifting results
require explicit names, algorithms and moduli; the existing noncomputable Hahn
and normal-form theorems alone do not establish them. Structural classification
and index-complexity claims require computability and descriptive-set-theoretic
inputs. The source's algebraic-root closure corollary retains its explicit
**nonzero polynomial** hypothesis. Its
[reconciliation notes](foundations-and-computation/computable-surreals/MERGE_NOTES.md)
and [review scope](foundations-and-computation/computable-surreals/REVIEW_SCOPE.md)
distinguish imported results, finite checks and the historical repository snapshot
from new Lean proofs.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:main` (line 263) | Numerically conservative effective core |
| Proposition | `prop:topology` (line 360) | No small nontrivial convergence in the fine order topology |
| Theorem | `thm:known` (line 434) | Known structural classification |
| Proposition | `prop:structring` (line 456) | Structural ring compilation and computable cuts |
| Proposition | `prop:structcount` (line 490) | Computable ordinals and lack of an exhaustive enumeration |
| Proposition | `prop:haltingreal` (line 515) | A halting real with a structural name |
| Corollary | Line 555 (unlabeled) | A structural--numerical incompatibility |
| Proposition | `prop:ordinal-boundary` (line 566) | Birthday and ordinal boundary |
| Proposition | `prop:validity` (line 593) | Validity has full well-foundedness complexity |
| Theorem | `thm:signtrap` (line 648) | The signed-order presentation trap |
| Theorem | `thm:badproduct` (line 713) | Decidable supports with a noncomputable product |
| Corollary | Line 777 (unlabeled) | Untitled |
| Theorem | `thm:singlefiber` (line 792) | Sparse Hahn multiplication can compute the halting set |
| Theorem | `thm:convolution-jump` (line 865) | One jump for coefficients, not for an ordinary output name |
| Proposition | `prop:realslice` (line 931) | Well-definedness and the real slice |
| Proposition | `prop:jets` (line 962) | Certified truncation |
| Theorem | `thm:ring` (line 1002) | Uniform numerical ring arithmetic |
| Lemma | `lem:gap` (line 1043) | Gap extraction without normalization |
| Lemma | `lem:geom` (line 1065) | Effective geometric series |
| Theorem | `thm:inverse` (line 1103) | Field closure and certified inversion |
| Proposition | `prop:residue` (line 1145) | Value group and effective residue |
| Theorem | `thm:hensel` (line 1183) | Effective simple Hensel lifting |
| Lemma | `lem:Rcclosed` (line 1258) | Untitled |
| Lemma | `lem:valuationRC` (line 1302) | A real-closedness criterion |
| Theorem | `thm:Lcrealclosed` (line 1331) | Real closedness of the effective core |
| Corollary | Line 1353 (unlabeled) | Algebraic operations on individual computable surreals |
| Proposition | `prop:puiseuxarithmetic` (line 1383) | Embedding and arithmetic |
| Theorem | `thm:puiseuxclosed` (line 1408) | A proper real-closed subfield |
| Lemma | `C-lem:finite-jet` (line 1513) | Finite-jet lifting |
| Corollary | `C-cor:laurent-lift` (line 1595) | Laurent version |
| Theorem | `C-thm:pc-realclosed` (line 1613) | Real-closedness of the operational model |
| Corollary | Line 1637 (unlabeled) | Untitled |
| Proposition | `C-prop:unit-hensel` (line 1681) | Unit-derivative lifting |
| Theorem | `thm:completion` (line 1767) | Effective sequential completeness |
| Theorem | `thm:completioncharacter` (line 1797) | Effective completion characterization |
| Proposition | `prop:nonmodulus` (line 1822) | A computable Cauchy sequence without a computable limit |
| Theorem | `thm:coefficient-limit` (line 1853) | Uniform coefficientwise limits on a fixed lattice |
| Theorem | `thm:inversehard` (line 1902) | Valuation, inversion, and sign obstructions |
| Theorem | `thm:nogo` (line 1952) | A representation-independent incompatibility |
| Theorem | `thm:jump` (line 1979) | Normalization has halting degree on computable indices |
| Theorem | `thm:root-obstructions` (line 2011) | Root-selection obstructions |
| Proposition | `prop:root-jump` (line 2036) | Certified square root and the extended halting threshold |
| Proposition | `prop:exactcoeffs` (line 2080) | Exact coefficients permit leading-term search |
| Proposition | `prop:diagonal` (line 2112) | A coefficient diagonal |
| Theorem | `thm:evaluation` (line 2139) | Effective infinitesimal evaluation |
| Theorem | `thm:integration` (line 2213) | Effective differentiation and the formal residue obstruction |
| Corollary | `cor:differential-quotient` (line 2267) | Kernel, image, and quotient of the formal derivative |
| Proposition | `prop:ode-obstruction` (line 2294) | A simple differential equation outside the workspace |
| Proposition | `prop:complexification` (line 2321) | Effective complexification |
| Proposition | `prop:modulus` (line 2362) | Squared modulus is uniform; modulus is not |
| Theorem | `thm:iterated` (line 2413) | Iterated numerically conservative real-closed fields |
| Theorem | `thm:parallel-towers` (line 2502) | Two compatible finite-rank hierarchies |
| Proposition | `prop:tower-jump` (line 2534) | Finite rank does not require iterated jumps |
| Theorem | `thm:oracle-fields` (line 2568) | Relativization and exact degree embeddings |
| Proposition | `prop:oracle-unions` (line 2601) | Unrestricted oracle unions |
| Proposition | `prop:neumanninterface` (line 2633) | An effective Neumann interface |

### expanding-polynomial-dynamics

Source: [surcomplex/expanding-polynomial-dynamics/article.tex](surcomplex/expanding-polynomial-dynamics/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `epd:lem:ideal` (line 506) | Untitled |
| Lemma | `epd:lem:evaluation` (line 564) | Finite-parameter Hahn evaluation |
| Lemma | `epd:lem:formalbranch` (line 638) | Universal implicit branch |
| Proposition | `epd:prop:branches` (line 669) | Exact branch metric |
| Theorem | `epd:thm:centers` (line 725) | Universal centers and common support |
| Corollary | `epd:cor:constant-center` (line 777) | Constant coefficients |
| Theorem | `epd:thm:fibers` (line 801) | Exact fibers and exact separation |
| Corollary | `epd:cor:cylinders` (line 847) | Exact finite cylinders |
| Corollary | `epd:cor:fiber-bijection` (line 858) | The action on the fibers |
| Theorem | `epd:thm:periodic` (line 877) | All preperiodicity equations split |
| Proposition | `epd:prop:multiplier` (line 922) | Exact multipliers |
| Corollary | `epd:cor:zeta` (line 943) | Periodic counts and zeta series |
| Theorem | `epd:thm:topology` (line 972) | Order-unit dichotomy |
| Proposition | `epd:prop:scalequotient` (line 1058) | Untitled |
| Theorem | `epd:thm:compact` (line 1078) | Compact-subsystem rigidity |
| Theorem | `epd:thm:extension` (line 1132) | Scalar-extension theorem |
| Theorem | `epd:thm:deformation` (line 1219) | Uniform deformation estimate |
| Corollary | `epd:cor:flatdeform` (line 1276) | Deformations invisible at all dynamical orders |
| Theorem | `epd:thm:bounded` (line 1318) | Exact bounded-orbit locus |
| Corollary | `epd:cor:coarsebounded` (line 1384) | Untitled |
| Proposition | `epd:prop:budget` (line 1419) | An orbit and difference budget |
| Theorem | `epd:thm:general` (line 1449) | Universal native equicontinuity criterion |
| Corollary | `epd:cor:empty-affine` (line 1492) | Untitled |
| Theorem | `epd:thm:surreal` (line 1562) | A surcomplex full shift with infinitesimal fibers |
| Corollary | `epd:cor:surreal-all` (line 1724) | Untitled |

### hahn-herglotz-positivity

Source: [surcomplex/hahn-herglotz-positivity/article.tex](surcomplex/hahn-herglotz-positivity/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `herg:lem:leadingvector` (line 208) | Leading-vector test |
| Lemma | `herg:lem:scalar` (line 289) | First nonzero real part |
| Corollary | `herg:cor:scalarnormal` (line 306) | Scalar normalization |
| Theorem | `herg:thm:normalization` (line 319) | Hahn--Herglotz normalization |
| Theorem | `herg:thm:harnack` (line 384) | Uniform matrix Harnack comparison |
| Theorem | `herg:thm:nullideal` (line 476) | Exact null-ideal criterion; also \lbl{meas:thm:nullideal} |
| Corollary | `herg:cor:twoscale` (line 503) | Two-scale criterion |
| Theorem | `herg:thm:functional` (line 553) | Infinitesimal saturation of strictly positive functionals |
| Corollary | `herg:cor:rieszfailure` (line 587) | A Riesz-type representation obstruction |
| Theorem | `herg:thm:saturation` (line 610) | Toeplitz saturation and finite completions |
| Theorem | `herg:thm:representation` (line 653) | Exact coefficientwise representation test |
| Proposition | `herg:prop:measuretoeplitz` (line 689) | Untitled |
| Theorem | `herg:thm:negativeatom` (line 717) | All Toeplitz tests pass, but no positive measure exists |
| Theorem | `herg:thm:quadrature` (line 750) | Nonclosedness of the positive-measure cone |
| Theorem | `herg:thm:fejer` (line 774) | Nonclosure with a fixed Haar leading coefficient |
| Theorem | `herg:thm:schur` (line 810) | Exact Schur iteration and its internal poles |
| Corollary | `herg:cor:unitary` (line 852) | Untitled |
| Theorem | `herg:thm:hierarchy` (line 899) | Strict Hahn--Herglotz hierarchy |
| Theorem | `herg:thm:prefix` (line 977) | One finite prefix admits every boundary behavior |
| Proposition | `herg:prop:transport` (line 1015) | Normal-form transport |

### hahn-tate-uniformization

Source: [surcomplex/hahn-tate-uniformization/article.tex](surcomplex/hahn-tate-uniformization/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `tate:thm:main` (line 251) | Exact-domain Hahn--Tate uniformization |
| Theorem | `tate:thm:arithmetic-main` (line 309) | Exact arithmetic and scalar extension |
| Corollary | `tate:cor:surcomplex-main` (line 331) | Surcomplex elliptic curves |
| Lemma | `tate:lem:neumann` (line 548) | Positive-support calculus |
| Lemma | `tate:node:lem:implicit` (line 604) | Formal inverse and implicit function |
| Lemma | `tate:lem:normalize` (line 654) | Finite normalization |
| Theorem | `tate:thm:theta` (line 735) | Theta domain |
| Proposition | `tate:prop:theta-product` (line 786) | Product and zeros |
| Theorem | `tate:thm:coordinates` (line 844) | Coordinate domain and support certificate |
| Proposition | `tate:prop:tail` (line 889) | Exact finite-tail bound |
| Proposition | `tate:prop:discriminant` (line 914) | Discriminant and modular invariant |
| Proposition | `tate:prop:differential` (line 946) | Differential and inversion identities |
| Lemma | `tate:lem:coarse-eval` (line 1009) | Unrestricted coarse formal evaluation |
| Lemma | `tate:lem:rank-one` (line 1076) | Completeness of the residue workspace |
| Theorem | `tate:thm:classical` (line 1121) | Tate; external classical input |
| Lemma | `tate:lem:formal-identity` (line 1152) | A universal formal parameter |
| Lemma | `tate:lem:agreement` (line 1231) | Agreement of Taylor and Hahn evaluation |
| Proposition | `tate:prop:identityfiber` (line 1354) | The whole coarse identity fiber |
| Corollary | `tate:cor:diagram` (line 1410) | Reduction and infinitesimal lifting |
| Proposition | `tate:node:prop:annulus` (line 1544) | Summability on the wide annulus |
| Theorem | `tate:node:thm:node` (line 1634) | Explicit formal smoothing coordinates |
| Proposition | `tate:node:prop:coefficients` (line 1668) | First inverse coefficients |
| Theorem | `tate:node:thm:nodalsurj` (line 1690) | Nodal inverse over a Hahn field |
| Lemma | `tate:node:lem:nodalnormalization` (line 1719) | Normalization of the special cubic |
| Proposition | `tate:node:prop:smooth` (line 1736) | Smooth-residue inverse |
| Lemma | `tate:node:lem:infinityvalues` (line 1779) | The valuation pattern at infinity |
| Proposition | `tate:node:prop:infinity` (line 1800) | Formal inverse at infinity |
| Theorem | `tate:node:thm:surjectivity` (line 1842) | Constructive surjectivity |
| Lemma | `tate:node:lem:generic` (line 1909) | Tate's generic-pair lemma |
| Theorem | `tate:node:thm:group` (line 1928) | Group uniformization |
| Theorem | `tate:node:thm:main` (line 1947) | Theorem~\ref{tate:thm:main} over any coefficient field of characteristic zero |
| Theorem | `tate:node:thm:support` (line 1982) | Equality of generated support monoids |
| Corollary | `tate:node:cor:monoidal` (line 2001) | Exact monoidal descent |
| Lemma | `tate:node:lem:isometry` (line 2032) | Valuation isometry |
| Corollary | `tate:node:cor:bidisk` (line 2060) | The node chart on the infinitesimal bidisk |
| Theorem | `tate:node:thm:moving` (line 2070) | Two-period comparison |
| Corollary | `tate:node:cor:fixedmetric` (line 2086) | Fixed-period distance and coordinate size |
| Corollary | `tate:node:cor:periodsensitivity` (line 2105) | Exact period sensitivity |
| Theorem | `tate:thm:extension` (line 2157) | Exponent embeddings preserve uniformization |
| Theorem | `tate:thm:tropical` (line 2212) | The valuation quotient |
| Proposition | `tate:node:prop:residue` (line 2327) | Fine residue sequence |
| Theorem | `tate:node:thm:obstruction` (line 2344) | No full-domain extension with the same kernel |
| Theorem | `tate:thm:recover` (line 2392) | Unique, support-preserving recovery |
| Corollary | `tate:cor:negativej` (line 2434) | Negative-$j$ uniformization |
| Lemma | `tate:lem:radical` (line 2477) | A single radical extension |
| Theorem | `tate:thm:torsion` (line 2518) | The complete torsion field |
| Corollary | `tate:cor:lattice` (line 2571) | A finite-lattice degree formula |
| Theorem | `tate:thm:surcomplex` (line 2619) | Surcomplex uniformization |
| Corollary | `tate:node:cor:real` (line 2663) | Real surreal case and transferred refinements |
| Theorem | `tate:theta:thm:positive` (line 2992) | Finite positive generation |
| Lemma | `tate:theta:lem:acute` (line 3013) | Finite acute generating families |
| Lemma | `tate:theta:lem:allocation` (line 3046) | Distributing lower-level coefficients |
| Lemma | `tate:theta:lem:shift` (line 3067) | A shift dominates every fixed mixed term |
| Lemma | `tate:theta:lem:latticeprojection` (line 3190) | Untitled |
| Lemma | `tate:theta:lem:onelevel` (line 3220) | One-level quadratic criterion |
| Theorem | `tate:theta:thm:flag` (line 3267) | Exact flag criterion |
| Corollary | `tate:theta:cor:domain` (line 3331) | The exact linear domain |
| Lemma | `tate:theta:lem:shuffle` (line 3363) | A finite interleaving bound |
| Theorem | `tate:theta:thm:ordinal` (line 3379) | Exact ordinal support law |
| Corollary | `tate:theta:cor:surrealordinal` (line 3424) | Actual surreal support lengths |
| Theorem | `tate:theta:thm:units` (line 3454) | Exact domain and unit robustness |
| Corollary | `tate:theta:cor:norepair` (line 3509) | No repair by units or ordered scalar extension |
| Corollary | `tate:theta:cor:rankone` (line 3526) | One-dimensional and diagonal domains |
| Theorem | `tate:theta:thm:certificate` (line 3592) | Finite minimum certificate |
| Corollary | `tate:theta:cor:voronoi` (line 3624) | Finite higher-rank Voronoi inequalities |
| Theorem | `tate:theta:thm:minimizers` (line 3650) | Finite minimizer geometry |
| Corollary | `tate:theta:cor:BFS` (line 3692) | Complete finite enumeration after one minimum |
| Lemma | `tate:theta:lem:implicit` (line 3742) | Implicit substitution with a Hahn certificate |
| Theorem | `tate:theta:thm:zerolift` (line 3800) | Smooth initial zeros lift |
| Corollary | `tate:theta:cor:notentire` (line 4006) | Untitled |

### holonomic-rigidity-for-entire-hahn-functions

Source: [surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex](surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `hol:lem:support` (line 498) | Hahn--Neumann support calculus and the positive monoid |
| Lemma | `hol:lem:nonincreasing` (line 544) | The nonincreasing leading-exponent obstruction |
| Lemma | `hol:lem:certificate` (line 562) | Two sufficient certificates |
| Lemma | `hol:lem:inward` (line 598) | Inward stability of strong evaluation |
| Proposition | `hol:prop:closure` (line 685) | Closure |
| Proposition | `hol:prop:faithful` (line 707) | Faithfulness of evaluation |
| Lemma | `hol:lem:escape` (line 769) | Escape chain |
| Theorem | `hol:thm:escapeexclusion` (line 810) | Evaluation exclusion criterion |
| Corollary | `hol:cor:boundedcost` (line 843) | Uniform bounded cost; no divisibility |
| Corollary | `hol:cor:periodic` (line 866) | Refined periodic threshold; requires $\Gamma$ divisible |
| Lemma | `hol:lem:integer` (line 912) | Integer evaluation |
| Lemma | `hol:lem:affine` (line 940) | Eventually affine valuation |
| Theorem | `hol:thm:unitorbit` (line 980) | Unit-orbit valuations |
| Lemma | `hol:lem:drec` (line 1095) | Differential coefficient recurrence |
| Proposition | `hol:prop:precursive` (line 1127) | Uniform obstruction for P-recursive coefficients |
| Proposition | `hol:prop:expdomain` (line 1189) | Formal exponential domain |
| Corollary | `hol:cor:algebraic` (line 1236) | Algebraic entire series |
| Corollary | `hol:cor:systems` (line 1254) | Rational differential systems |
| Proposition | `hol:prop:inhomogeneous` (line 1268) | Rational inhomogeneous equations |
| Lemma | `hol:lem:generic` (line 1334) | Avoiding countably many polynomial conditions |
| Corollary | `hol:cor:multialg` (line 1398) | Multivariate algebraic rigidity |
| Lemma | `hol:lem:qrec` (line 1421) | Dilation coefficient recurrence |
| Corollary | `hol:cor:unitrigid` (line 1458) | Every unit dilation is globally rigid |
| Proposition | `hol:prop:noncofinal` (line 1488) | Noncofinal dilation scales force polynomiality |
| Theorem | `hol:thm:coarse` (line 1548) | Coarsened exclusion |
| Theorem | `hol:thm:thetadomain` (line 1610) | Exact partial theta domain |
| Proposition | `hol:prop:torsion` (line 1814) | Torsion covariance |
| Lemma | `hol:lem:bivariate` (line 1863) | Polynomial dependence on the index as well as the dilation |
| Theorem | `hol:thm:mixed` (line 1882) | Mixed rigidity at a noncofinal nonzero scale |
| Corollary | `hol:cor:universal` (line 1950) | Universal nontorsion dilation rigidity |
| Theorem | `hol:thm:explicit` (line 1968) | An explicit universally nonholonomic entire series |
| Corollary | `hol:cor:detect` (line 2090) | Detecting order units by functional equations |
| Lemma | `hol:nl:lem:algebra` (line 2401) | Hahn-family algebra and its residue |
| Corollary | `hol:nl:cor:gauss` (line 2442) | Gauss multiplicativity |
| Lemma | `hol:nl:lem:derivatives` (line 2480) | Exact derivative scaling |
| Lemma | `hol:nl:lem:active` (line 2497) | Large active degrees |
| Lemma | `hol:nl:lem:corner` (line 2563) | The exact corner identity |
| Theorem | `hol:nl:thm:certificate` (line 2596) | Nonlinear finite exclusion certificate |
| Corollary | `hol:nl:cor:cofinal` (line 2691) | Cofinal scales suffice |
| Theorem | `hol:nl:thm:degrees` (line 2755) | Finite candidate degrees |
| Corollary | `hol:nl:cor:locus` (line 2800) | An algebraic entire-solution locus |
| Proposition | `hol:nl:prop:riccati` (line 2846) | Two exact Riccati classifications |
| Theorem | `hol:nl:thm:nouniform` (line 2891) | A fixed Riccati equation defeats every uniform bound |
| Theorem | `hol:nl:thm:corner` (line 2940) | Higher-order corner criterion and its boundary |
| Proposition | `hol:nl:prop:higherdegrees` (line 2959) | Higher-order degree candidates |
| Proposition | `hol:nl:prop:painleve` (line 2980) | The first two Painlev\'e polynomial equations |
| Proposition | `hol:nl:prop:degenerate` (line 3020) | Complete formal classification of the example |
| Theorem | `hol:nl:thm:euler` (line 3089) | Positive-weight Euler rigidity |
| Corollary | `hol:nl:cor:eulerdegrees` (line 3150) | Weighted-degree candidates |
| Corollary | `hol:nl:cor:theta` (line 3214) | Two independent jets of the quadratic-exponent series |
| Corollary | `hol:nl:cor:infiniterank` (line 3237) | An example without an order unit |

### infinite-dimensional-hahn-spectral-theory

Source: [surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex](surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `ihs:hh:thm:package` (line 414) | Part I theorem package |
| Lemma | `ihs:lem:support` (line 711) | Classical Hahn--Neumann support lemma |
| Lemma | `ihs:lem:neumann` (line 767) | Support-certified Neumann inverse |
| Corollary | `ihs:cor:evaluate` (line 796) | Evaluation of homogeneous constructions |
| Corollary | `ihs:cor:binomial` (line 813) | Formal power series at a positive-support argument |
| Proposition | `ihs:prop:unify` (line 950) | The algebra-relative spectra of constant elements |
| Proposition | `ihs:hh:prop:inner` (line 1088) | Positive-definite scalar extension |
| Theorem | `ihs:hh:thm:adjoint` (line 1143) | Automatic adjoint structure |
| Corollary | `ihs:hh:cor:autobounded` (line 1199) | Automatic summability and boundedness |
| Theorem | `ihs:hh:thm:defect` (line 1239) | Positive-order defect rigidity |
| Corollary | `ihs:hh:cor:norepair` (line 1279) | No positive-order repair |
| Corollary | `ihs:hh:cor:independent` (line 1286) | Explicit independent obstruction classes |
| Lemma | `ihs:hh:lem:normalgap` (line 1340) | Normal isolated-point decomposition |
| Theorem | `ihs:hh:thm:spectrum` (line 1361) | Accumulation-monad spectrum |
| Theorem | `ihs:hh:thm:point` (line 1428) | No new normal eigenvalues |
| Corollary | `ihs:hh:cor:reality` (line 1475) | A sharp spectral-reality criterion |
| Corollary | `ihs:hh:cor:compact` (line 1503) | Ordinary compact normal extension |
| Corollary | `ihs:hh:cor:extension` (line 1545) | Persistence under ordered-group extension |
| Theorem | `ihs:hh:thm:smooth` (line 1575) | All inverse moments are necessary and sufficient |
| Lemma | `ihs:hh:lem:continuum` (line 1659) | Continuum many independent defect vectors |
| Theorem | `ihs:hh:thm:continuum` (line 1676) | Every positive-order perturbation retains a large defect |
| Theorem | `ihs:hh:thm:coercive` (line 1712) | A coercive noninvertible self-adjoint operator |
| Corollary | `ihs:hh:cor:lax` (line 1748) | Failure of a specified Lax--Milgram analogue |
| Proposition | `ihs:hh:prop:complete` (line 1790) | Rank-one valuation completeness |
| Theorem | `ihs:hh:thm:closedrange` (line 1818) | Closed-range orthogonality failure |
| Proposition | `ihs:hh:prop:riesz` (line 1857) | Explicit failure of valuation Riesz representation |
| Lemma | `ihs:hh:lem:contract` (line 1901) | Ordinary contraction bounds survive |
| Theorem | `ihs:hh:thm:norm` (line 1920) | Norm-attainment criterion |
| Lemma | `ihs:rf:lem:rcf` (line 2137) | Untitled |
| Proposition | `ihs:rf:prop:algebra` (line 2176) | Untitled |
| Proposition | `ihs:rf:prop:inner` (line 2201) | Untitled |
| Lemma | `ihs:rf:lem:strongaction` (line 2242) | Strong sums are respected |
| Theorem | `ihs:rf:thm:similarity` (line 2282) | Coherent simple-residue diagonalization |
| Theorem | `ihs:rf:thm:unitary` (line 2352) | Normalized infinite Hahn spectral theorem |
| Corollary | `ihs:rf:cor:scales` (line 2410) | No new scales |
| Theorem | `ihs:rf:thm:synthesis` (line 2491) | Exact Hahn spectral synthesis |
| Theorem | `ihs:rf:thm:commutant` (line 2557) | The complete commutant |
| Corollary | `ihs:rf:cor:projsums` (line 2588) | Projection sums are pointwise Hahn sums |
| Theorem | `ihs:rf:thm:resolvent` (line 2678) | Coherent resolvents at every noneigenvalue |
| Corollary | `ihs:rf:cor:forcing` (line 2741) | The inhomogeneous equation |
| Lemma | `ihs:rf:lem:finitewalks` (line 2772) | Finite walks at a prescribed weight |
| Theorem | `ihs:rf:thm:walks` (line 2785) | Coefficientwise walk dependence |
| Theorem | `ihs:rf:thm:marked` (line 2838) | Exact marked-walk stability |
| Theorem | `ihs:rf:thm:finite` (line 2893) | Finite-section exactness |
| Corollary | `ihs:rf:cor:radius` (line 2926) | One-scale radius bound |
| Theorem | `ihs:rf:thm:sharp` (line 2948) | A nonzero first boundary coefficient |
| Proposition | `ihs:rf:prop:closed` (line 3031) | An exact branch and its eigenvector |
| Proposition | `ihs:rf:prop:noconv` (line 3143) | Why geometric partial sums need not converge |
| Proposition | `ihs:rf:prop:bounded` (line 3168) | The inverse-gap obstruction |
| Proposition | `ihs:rf:prop:degenerate` (line 3212) | A positive Hahn operator with no eigenvectors |
| Proposition | `ihs:rf:prop:incoherent` (line 3245) | Failure without global support coherence |
| Corollary | `ihs:rf:cor:surcomplex` (line 3270) | An infinite surcomplex spectral system |
| Proposition | `ihs:rf:prop:extension` (line 3292) | Naturality and absence of new spectral points |
| Lemma | `ihs:dz:lem:laurent` (line 3627) | Laurent inverse criterion |
| Lemma | `ihs:dz:lem:straighten` (line 3672) | Strong parameter straightening |
| Lemma | `ihs:dz:lem:projection` (line 3730) | Cyclic-support inverse descent |
| Theorem | `ihs:dz:thm:descent` (line 3756) | Arbitrary-parameter inverse descent |
| Theorem | `ihs:dz:thm:halo` (line 3788) | Constant-element spectrum |
| Theorem | `ihs:dz:thm:scale` (line 3812) | Exact valuation and leading coefficient |
| Corollary | `ihs:dz:cor:workspace` (line 3836) | Workspace invariance |
| Corollary | `ihs:dz:cor:normal` (line 3892) | Recovery of the normal case |
| Corollary | `ihs:dz:cor:algebraic` (line 3943) | Algebraicity criterion |
| Lemma | `ihs:dz:lem:powers` (line 3986) | Power image |
| Lemma | `ihs:dz:lem:local` (line 4000) | Exact local polynomial image |
| Lemma | `ihs:dz:lem:commuting` (line 4024) | Commuting factors |
| Proposition | `ihs:dz:prop:ordinarymapping` (line 4034) | Ordinary polynomial mapping |
| Theorem | `ihs:dz:thm:image` (line 4061) | Exact ramified spectral image |
| Lemma | `ihs:dz:lem:group` (line 4089) | Finite unions of integer-multiple subgroups |
| Theorem | `ihs:dz:thm:criterion` (line 4108) | Sharp spectral-mapping criterion |
| Proposition | `ihs:dz:prop:polemap` (line 4140) | Pole-order profile |
| Theorem | `ihs:dz:thm:surcomplex` (line 4317) | Surcomplex halo classification |
| Corollary | `ihs:dz:cor:fullmapping` (line 4337) | Polynomial mapping for the full surcomplex scalars |
| Lemma | `ihs:fr:lem:lift` (line 4592) | Identity lifting |
| Proposition | `ihs:fr:prop:continuum` (line 4645) | The size of a compact range defect |
| Corollary | `ihs:fr:cor:reservoir` (line 4678) | The infinitesimal reservoir |
| Proposition | `ihs:fr:prop:riesz` (line 4711) | Untitled |
| Lemma | `ihs:fr:lem:rotation` (line 4735) | Support-controlled direct rotation |
| Lemma | `ihs:fr:lem:hermitian` (line 4769) | Finite Hermitian diagonalization |
| Theorem | `ihs:fr:thm:cluster` (line 4787) | Exact isolated-cluster reduction |
| Theorem | `ihs:fr:thm:main` (line 4829) | Compact-residue spectral classification |
| Corollary | `ihs:fr:cor:essential` (line 4883) | Untitled |
| Corollary | `ihs:fr:cor:extension` (line 4902) | Fixed point spectrum, growing spectral monad |
| Theorem | `ihs:fr:thm:nounitary` (line 4955) | No global bounded-coefficient Hahn unitary |
| Proposition | `ihs:fr:prop:eigencoeff` (line 4999) | The eigenvalue list is not a bounded coefficient |
| Proposition | `ihs:fr:prop:detidentities` (line 5086) | Determinant identities |
| Lemma | `ihs:fr:lem:correction` (line 5117) | Ordinary finite-rank correction |
| Theorem | `ihs:fr:thm:fredholm` (line 5131) | Hahn Fredholm alternative |
| Theorem | `ihs:fr:thm:nolidskii` (line 5187) | Failure of the spectral trace sum |
| Theorem | `ihs:fr:thm:noproduct` (line 5217) | Failure of a spectral product formula |
| Theorem | `ihs:fr:thm:coupling` (line 5272) | Exact finite-coupling detection |
| Proposition | `ihs:fr:prop:negeval` (line 5291) | Negative-valuation evaluation can fail |
| Lemma | `ihs:fr:lem:nonvanishing` (line 5320) | A nonzero coherent germ cannot vanish on a whole monad |
| Theorem | `ihs:fr:thm:nocharacteristic` (line 5339) | No analytic characteristic determinant at the accumulation point |

### prony-reconstruction-at-surreal-scales

Source: [surcomplex/prony-reconstruction-at-surreal-scales/article.tex](surcomplex/prony-reconstruction-at-surreal-scales/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `prony:thm:main` (line 150) | Optimal uniform reconstruction |
| Lemma | `prony:lem:support` (line 383) | Positive-support evaluation |
| Lemma | `prony:lem:hensel` (line 412) | Residue-simple lifting |
| Corollary | `prony:cor:actual` (line 455) | Actual surreal and surcomplex data |
| Proposition | `prony:prop:prony` (line 490) | Classical Prony uniqueness |
| Lemma | `prony:lem:cofactorbound` (line 547) | Uniform estimate in cofactor coordinates |
| Lemma | `prony:lem:localroots` (line 566) | Cofactor localization |
| Lemma | `prony:lem:pade` (line 628) | Finite Pad\'e identity |
| Lemma | `prony:lem:cross` (line 649) | Cross-numerator control |
| Lemma | `prony:lem:weight` (line 671) | Weight errors without a second conditioning loss |
| Corollary | `prony:cor:positive` (line 744) | Real and positive data |
| Proposition | `prony:prop:last` (line 773) | The last-moment formula |
| Proposition | `prony:prop:rows` (line 974) | Exact row losses |
| Proposition | `prony:prop:lattice` (line 1011) | Finite coefficient criterion |
| Corollary | `prony:cor:nonlinear` (line 1055) | Exact nonlinear uncertainty set |
| Theorem | `prony:thm:graph` (line 1123) | Nonuniform reconstruction certificate |
| Proposition | `prony:prop:nonlinearobstruction` (line 1320) | A nonlinear obstruction to the cancellation gain |

### wick-summability-certificates

Source: [surcomplex/wick-summability-certificates/article.tex](surcomplex/wick-summability-certificates/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `wick:lem:neumann` (line 361) | Neumann's positive-support lemma, classical |
| Corollary | `wick:cor:substitution` (line 373) | Finite infinitesimal substitution |
| Proposition | `wick:prop:embedding` (line 409) | Surcomplex realization |
| Lemma | `wick:lem:wickcount` (line 499) | Colored matching multiplicity |
| Lemma | `wick:lem:dickson` (line 568) | Dickson's finiteness lemma, classical |
| Proposition | `wick:prop:hilbert` (line 585) | A finite Hilbert basis |
| Proposition | `wick:prop:module` (line 606) | Finite generation of every observable sector |
| Theorem | `wick:thm:alternative` (line 642) | Strict rational alternative |
| Theorem | `wick:thm:main` (line 730) | Exact diagramwise Hahn domain |
| Corollary | `wick:cor:obstruction` (line 801) | A computable obstruction pattern |
| Corollary | `wick:cor:robustness` (line 813) | Valuation robustness and diagonal invariance |
| Lemma | `wick:lem:indecompconnected` (line 865) | Indecomposable counts force connectedness |
| Lemma | `wick:lem:rewire` (line 877) | Cyclic connected amplification |
| Theorem | `wick:thm:connected` (line 921) | Equality of connected and full diagramwise domains |
| Proposition | `wick:prop:connectedlog` (line 949) | Specialization of the connected identity |
| Lemma | `wick:lem:valCS` (line 1008) | Valuation Cauchy--Schwarz |
| Theorem | `wick:thm:positive` (line 1027) | Positive-covariance criterion |
| Corollary | `wick:cor:stationary` (line 1104) | Sharp multiscale power counting |
| Lemma | `wick:lem:ibp` (line 1165) | Algebraic Gaussian integration by parts |
| Theorem | `wick:thm:SD` (line 1184) | Exact perturbative Schwinger--Dyson identities |
| Proposition | `wick:prop:tail` (line 1238) | A valuation error estimate |
| Proposition | `wick:prop:quarticH` (line 1384) | Exact quartic Hilbert basis and irredundant tests |
| Proposition | `wick:prop:signcoherent` (line 1522) | Sign-coherent equivalence |

### hahn-valued-measures-and-probability

Source: [surreal/hahn-valued-measures-and-probability/article.tex](surreal/hahn-valued-measures-and-probability/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `meas:lem:sumalgebra` (line 555) | Regrouping, products, and positivity |
| Lemma | `meas:lem:coefpositive` (line 593) | Positivity of coefficientwise sums |
| Lemma | `meas:lem:boolean` (line 841) | Infinite Boolean algebras contain disjoint sequences |
| Lemma | `meas:lem:scalar` (line 856) | Disjoint-finite scalar measures are finitely point-atomic; sources 10 and 11 |
| Proposition | `meas:prop:coefficients` (line 918) | Finite coefficient measures |
| Lemma | `meas:lem:global` (line 948) | Automatic common well-order; source 11 |
| Theorem | `meas:thm:atomic` (line 977) | Atomic classification with automatic common support; sources 10 and 11 |
| Corollary | `meas:cor:coefficient-test` (line 1027) | Coefficientwise criterion without a support hypothesis; source 10 |
| Corollary | `meas:cor:two-axioms` (line 1070) | The two axioms on countably separated spaces |
| Corollary | `meas:cor:shadow` (line 1101) | Finite real shadow of a strong probability; sources 10 and 11 |
| Corollary | `meas:cor:cardinality` (line 1124) | Cardinality of the atomic set; source 10 |
| Proposition | `meas:prop:integration` (line 1170) | Pushforward and scalar-valued integration; sources 10 and 11 |
| Theorem | `meas:thm:orbits` (line 1248) | Finite-orbit rigidity; source 15 |
| Corollary | `meas:cor:transitive` (line 1281) | No transitive invariant strong probability; source 11 |
| Corollary | `meas:cor:exchangeable` (line 1295) | Exchangeability collapses; source 15 |
| Corollary | `meas:cor:actual` (line 1371) | Actual surreal atomicity; source 10 |
| Lemma | `meas:lem:tree` (line 1410) | Bounded-width coherent scalar trees |
| Theorem | `meas:thm:cylinder` (line 1435) | Exact strong cylinder-extension criterion; source 10 |
| Corollary | `meas:cor:positive-test` (line 1484) | Exact positivity test; source 10 |
| Lemma | `meas:lem:neumann` (line 1508) | Neumann support lemma, classical; stated by sources 10 and 15 |
| Lemma | `meas:lem:labeled` (line 1537) | Labelled words and subproducts |
| Proposition | `meas:prop:products` (line 1561) | Infinite products of infinitesimal perturbations |
| Lemma | `meas:lem:recover` (line 1596) | Recovering rare entries from first-error masses |
| Theorem | `meas:thm:independent` (line 1643) | Exact independent finite-state criterion; source 10 |
| Corollary | `meas:cor:bernoulli` (line 1751) | One-line Bernoulli criterion; source 10 |
| Theorem | `meas:thm:coarse` (line 1817) | Extension may fail after refining a valid binary law; source 10 |
| Proposition | `meas:prop:enlarge` (line 1862) | Absoluteness under exponent enlargement; source 10 |
| Lemma | `meas:lem:prony` (line 1916) | Finite signed moment sequences |
| Theorem | `meas:thm:momentcriterion` (line 1952) | Exact strong moment criterion; source 11 |
| Theorem | `meas:thm:visibility` (line 2040) | Finite visibility detects a negative atom; source 11 |
| Corollary | `meas:cor:hidden-necessary` (line 2066) | A necessary condition for hidden negative mass |
| Corollary | `meas:cor:safesupport` (line 2079) | The safe support range; source 11 |
| Theorem | `meas:thm:barrier` (line 2113) | Polynomial positivity barrier; source 11 |
| Corollary | `meas:cor:hermitianbarrier` (line 2142) | Hermitian and localizing forms; source 11 |
| Corollary | `meas:cor:multivariate` (line 2160) | Zariski-dense early atoms; source 11 |
| Theorem | `meas:thm:continuousbarrier` (line 2182) | Continuous-test barrier; source 11 |
| Proposition | `meas:prop:hidden-positive` (line 2241) | Every finite-dimensional law is nonnegative; source 10 |
| Theorem | `meas:thm:example` (line 2317) | Full positivity but no positive strong representation; source 11 |
| Corollary | `meas:cor:hausdorff` (line 2356) | All Hausdorff inequalities hold strictly; source 11 |
| Theorem | `meas:thm:threshold` (line 2443) | The $\omega+1$ threshold for strong measures; sources 10 and 11 |
| Lemma | `meas:lem:CB` (line 2527) | Strong atomic determinant formula; source 11 |
| Theorem | `meas:thm:determinants` (line 2560) | Every determinant scale and leading coefficient; source 11 |
| Corollary | `meas:cor:jacobi` (line 2630) | Explicit Jacobi scales; source 11 |
| Theorem | `meas:thm:gauss` (line 2670) | Finite Gaussian quadrature over a real closed field; source 11 |
| Lemma | `meas:lem:heine` (line 2719) | Orthogonal polynomial from atomic subsets; source 11 |
| Theorem | `meas:thm:quadratureresidues` (line 2746) | Standard parts and nonreal quadrature nodes; source 11 |
| Corollary | `meas:cor:actualNo` (line 2823) | No positive surreal strong measure for the moments; source 11 |
| Theorem | `meas:thm:extension` (line 2885) | Coefficientwise signed extension test; source 15 |
| Theorem | `meas:thm:nullideal` (line 2931) | Null-ideal positivity criterion; source 15, and independently source 18 |
| Corollary | `meas:cor:dominated` (line 3015) | Dominated corrections; source 15 |
| Theorem | `meas:thm:interior` (line 3076) | Interior extension criterion; source 15 |
| Lemma | `meas:lem:chaos` (line 3112) | Multilinear chaos bound; source 15 |
| Lemma | `meas:lem:L1lower` (line 3177) | Uniform $L^1$ lower bound; source 15 |
| Theorem | `meas:thm:boundary` (line 3227) | Boundary extension criterion; source 15 |
| Theorem | `meas:thm:mixed` (line 3376) | Mixed extension criterion; source 15 |
| Corollary | `meas:cor:iid` (line 3427) | No coefficientwise nonreal i.i.d.\ bias; source 15 |
| Proposition | `meas:prop:general-l1` (line 3508) | A universal $\ell^1$ sufficient condition; source 15 |
| Proposition | `meas:prop:complex` (line 3551) | Surcomplex analogue; source 15 |
| Proposition | `meas:prop:conditioning` (line 3572) | Conditioning on infinitesimal events; source 15 |

### markov-generators-at-every-scale

Source: [surreal/markov-generators-at-every-scale/article.tex](surreal/markov-generators-at-every-scale/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `markov:prop:forest` (line 650) | Classical matrix-forest identity |
| Theorem | `markov:thm:leading` (line 738) | The complete leading-forest formula |
| Proposition | `markov:prop:remainder` (line 793) | A valuation remainder certificate |
| Lemma | `markov:lem:resolvent` (line 838) | Resolvent compatibility |
| Theorem | `markov:thm:flag` (line 864) | Projection hierarchy |
| Lemma | `markov:lem:splitting` (line 934) | Classical splitting of a stochastic idempotent |
| Theorem | `markov:thm:effective` (line 987) | Effective-generator reconstruction |
| Corollary | `markov:cor:effective-semigroup` (line 1051) | A real semigroup on each retract |
| Theorem | `markov:thm:flag-realization` (line 1102) | Projection-flag realization |
| Lemma | `markov:lem:completion` (line 1144) | Irreducible completion invisible to the hierarchy |
| Theorem | `markov:thm:general-realization` (line 1211) | Prescribed-crossover realization |
| Corollary | `markov:cor:classification` (line 1316) | A necessary and sufficient criterion |
| Proposition | `markov:prop:reversible` (line 1334) | Full-support reversible flags |
| Theorem | `markov:thm:stability` (line 1394) | All-parameter, entrywise relative stability |
| Corollary | `markov:cor:leading-equivalence` (line 1426) | Leading data suffice simultaneously |
| Lemma | `markov:lem:separation` (line 1467) | Finite positive signs can be represented rationally |
| Theorem | `markov:thm:rank-one` (line 1515) | Simultaneous rank-one realization of the leading diagram |
| Lemma | `markov:lem:initial-spectrum` (line 1605) | Valuations and initial eigenvalue factors |
| Theorem | `markov:thm:char` (line 1644) | Effective characteristic and amplitude identity |
| Theorem | `markov:thm:convexity` (line 1694) | Discrete convexity and all eigenvalue valuations |

### tail-spans-and-differential-transcendence

Source: [surreal/tail-spans-and-differential-transcendence/article.tex](surreal/tail-spans-and-differential-transcendence/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `tail:lem:basechange` (line 290) | Finite base change |
| Lemma | `tail:lem:signs` (line 333) | Independent sign changes |
| Theorem | `tail:thm:coefficient` (line 381) | Coefficient-field criterion |
| Lemma | `tail:lem:stabilization` (line 455) | Stabilization and exceptions |
| Lemma | `tail:lem:multilinear` (line 477) | Cofinite spanning detects multilinear forms |
| Lemma | `tail:lem:difference` (line 500) | Top-degree mixed difference |
| Proposition | `tail:prop:orbit` (line 534) | Sign-orbit independence |
| Theorem | `tail:thm:tail` (line 578) | Exact tail-span classification |
| Theorem | `tail:thm:planes` (line 660) | Relation ideal as disjoint affine planes |
| Corollary | `tail:cor:finitewitness` (line 780) | Untitled |
| Theorem | `tail:thm:onesurreal` (line 881) | Every infinite subseries is differentially transcendental |
| Theorem | `tail:thm:surreal` (line 927) | Explicit maximal differential transcendence |
| Lemma | `tail:lem:analyticclasses` (line 1051) | Independent analytic square classes |
| Lemma | `tail:lem:expgraph` (line 1128) | Untitled |
| Lemma | `tail:lem:jetspan` (line 1151) | Hereditary full jet span |
| Theorem | `tail:thm:mixed` (line 1185) | Hereditary mixed differential independence |
| Theorem | `tail:thm:continuumanalytic` (line 1318) | Continuum many jointly independent mixed jets |
| Proposition | `tail:prop:halo` (line 1377) | Joint summability of the halo formula |
| Proposition | `tail:prop:functionalmeaning` (line 1407) | Untitled |
| Theorem | `tail:thm:closure` (line 1456) | Closure of the algebraic coefficient part |
| Proposition | `tail:prop:undecidable` (line 1523) | Untitled |

### three-duals-of-hahn-vector-spaces

Source: [surcomplex/three-duals-of-hahn-vector-spaces/article.tex](surcomplex/three-duals-of-hahn-vector-spaces/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `duals:thm:overview-completion` (line 196) | Completion and enlargement; proved in \cref{duals:sec:completion,duals:sec:enlargement} |
| Theorem | `duals:thm:overview-duals` (line 218) | Strong maps and the continuous dual; proved in \cref{duals:sec:strong,duals:sec:continuous} |
| Lemma | `duals:lem:support` (line 386) | Classical support facts |
| Lemma | `duals:lem:continuous-shift` (line 440) | Continuity is a uniform valuation-shift bound |
| Theorem | `duals:thm:strong` (line 483) | Global-support classification |
| Corollary | `duals:cor:strong-calculus` (line 548) | Operator calculus and automatic continuity |
| Proposition | `duals:prop:algebraic` (line 598) | Finite total coefficient rank |
| Theorem | `duals:thm:completion` (line 623) | Finite rank below every cut |
| Lemma | `duals:lem:group` (line 679) | An order-theoretic alternative |
| Theorem | `duals:thm:cyclic` (line 707) | The cyclic-group boundary |
| Theorem | `duals:thm:cofinality-completion` (line 736) | The cofinality boundary for nontrivial completion |
| Proposition | `duals:prop:spherical` (line 801) | Spherical completeness of the full Hahn space |
| Theorem | `duals:thm:HB` (line 855) | Contractive scalar extension |
| Lemma | `duals:lem:E-extension` (line 928) | Extension from constants to their algebraic span |
| Theorem | `duals:thm:restriction` (line 947) | Exact restriction sequence |
| Theorem | `duals:thm:separation` (line 985) | Separation of the completion defect |
| Corollary | `duals:cor:ghost-boundary` (line 1030) | Exact existence boundary |
| Theorem | `duals:thm:twofailures` (line 1051) | Two failures, for every noncyclic group |
| Corollary | `duals:cor:second-quotient` (line 1094) | A second quotient obstruction |
| Theorem | `duals:thm:continuous-strong` (line 1121) | When continuous and strong duals agree |
| Proposition | `duals:prop:norm` (line 1177) | Norm and valuation; standard coefficient extension |
| Proposition | `duals:prop:order-bound` (line 1223) | Order bounds for all continuous maps |
| Theorem | `duals:thm:infinite-bounds` (line 1262) | An ordinary unbounded functional has precisely infinite bounds |
| Theorem | `duals:thm:riesz` (line 1303) | Coefficientwise Riesz criterion and exact first gap |
| Corollary | `duals:cor:three-duals` (line 1374) | The three-dual trichotomy |
| Proposition | `duals:prop:dimension` (line 1401) | Untitled |
| Theorem | `duals:thm:hyperplane` (line 1451) | A closed, strongly complemented hyperplane with zero orthogonal complement |
| Theorem | `duals:thm:distance` (line 1512) | Exact lower-bound cut for the distance |
| Theorem | `duals:thm:basechange` (line 1558) | Cofinal preservation and noncofinal collapse |

### hidden-negative-hermitian-directions

Source: [surcomplex/hidden-negative-hermitian-directions/article.tex](surcomplex/hidden-negative-hermitian-directions/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `hnd:thm:preview` (line 171) | Maximal hidden negative inertia; preview |
| Proposition | `hnd:prop:evaluation` (line 561) | Closure under positive-order formal evaluation |
| Lemma | `hnd:lem:characterextension` (line 593) | Character extension and separation |
| Lemma | `hnd:lem:supportdegree` (line 631) | Algebraic degree bounds the support index |
| Proposition | `hnd:prop:probeclosed` (line 675) | Algebraic closedness of the probe field |
| Lemma | `hnd:lem:cyclicintersection` (line 726) | Untitled |
| Theorem | `hnd:thm:barrier` (line 755) | Uniform finite-lattice approximation barrier |
| Theorem | `hnd:thm:degree` (line 778) | Primorial approximation law |
| Corollary | `hnd:cor:degreebound` (line 835) | A degree-limited obstruction |
| Theorem | `hnd:thm:separation` (line 892) | Uniform linear-combination separation |
| Theorem | `hnd:thm:independence` (line 937) | Independent prime-tail family |
| Corollary | `hnd:cor:trdeg` (line 1012) | Untitled |
| Theorem | `hnd:thm:inertia` (line 1035) | Hidden-inertia construction |
| Corollary | `hnd:cor:smallmatrix` (line 1085) | Smallest example |
| Theorem | `hnd:thm:closedseparation` (line 1148) | The barrier persists through valuation closure |
| Proposition | `hnd:prop:lc` (line 1192) | Untitled |
| Corollary | `hnd:cor:lc` (line 1212) | Untitled |
| Proposition | `hnd:prop:density` (line 1235) | Quadratic testing characterizes order density |
| Theorem | `hnd:thm:surreal` (line 1318) | Workspace-independent surreal probe obstruction |
| Lemma | `hnd:lem:psdkernel` (line 1360) | Untitled |
| Theorem | `hnd:thm:twoscale` (line 1377) | Two-scale matrix positivity |
| Theorem | `hnd:thm:measure` (line 1564) | Two-scale matrix null ideals |
| Corollary | `hnd:cor:measurekernel` (line 1634) | Eventwise kernel and rank |
| Corollary | `hnd:cor:scalarmeasure` (line 1657) | Scalar specialization |

### transcendence-over-bounded-support

Source: [surreal/transcendence-over-bounded-support/article.tex](surreal/transcendence-over-bounded-support/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `bst:thm:mainintro` (line 147) | Optimal-support independence; proved in Section~\ref{bst:sec:independence} |
| Theorem | `bst:thm:descentintro` (line 169) | Cofinal coefficient--exponent descent; proved in Section~\ref{bst:sec:descent} |
| Lemma | `bst:lem:bounds` (line 309) | Elementary support bounds |
| Proposition | `bst:prop:localdensity` (line 330) | Localization and density |
| Lemma | `bst:lem:cofinality` (line 365) | Untitled |
| Lemma | `bst:lem:projection` (line 443) | Projection identity |
| Theorem | `bst:thm:descent` (line 475) | Simultaneous descent |
| Corollary | `bst:cor:relations` (line 515) | Intersection, relations, and algebraic degree |
| Corollary | `bst:cor:onescale` (line 553) | One cofinal scale |
| Lemma | `bst:lem:skeleton` (line 628) | Existence at the exact cofinality |
| Lemma | `bst:lem:detection` (line 681) | Support-band detection |
| Corollary | `bst:cor:onegap` (line 741) | A one-series version |
| Lemma | `bst:lem:coding` (line 771) | Cofinal finite-pattern realization |
| Lemma | `bst:lem:grid` (line 807) | Integer grids detect polynomials |
| Theorem | `bst:thm:independent` (line 825) | The sharp support theorem |
| Corollary | `bst:cor:optimal` (line 864) | Optimal cardinality and order type |
| Corollary | `bst:cor:perturb` (line 883) | Arbitrary bounded perturbations |
| Corollary | `bst:cor:balls` (line 896) | Independent families in every valuation ball |
| Corollary | `bst:cor:exactcard` (line 927) | Cardinality-matched groups |
| Corollary | `bst:cor:realgroup` (line 944) | Every nonzero real-exponent subgroup |
| Theorem | `bst:thm:explicit` (line 980) | Explicit multiplicative-parameter family |
| Theorem | `bst:thm:fieldcriterion` (line 1086) | Absence of a highest scale |
| Corollary | `bst:cor:closedbase` (line 1121) | Closed coefficient fields at unbounded rank |
| Proposition | `bst:prop:toprank` (line 1157) | Top-rank presentation |
| Proposition | `bst:prop:supimport` (line 1185) | Imported rank-one support theorem |
| Corollary | `bst:cor:units` (line 1196) | Units see exactly the highest rank |
| Theorem | `bst:thm:actualreal` (line 1265) | A continuum of independent actual infinitesimals |
| Theorem | `bst:thm:kappa` (line 1319) | Arbitrarily large, explicit-support surreal families |
| Theorem | `bst:thm:gcddescent` (line 1639) | Normalized GCD descent |
| Lemma | `bst:lem:characters` (line 1649) | Untitled |

### matrix-scaling-at-surreal-scales

Source: [surreal/matrix-scaling-at-surreal-scales/article.tex](surreal/matrix-scaling-at-surreal-scales/article.tex).

Statements remain **pending unless explicitly mapped** in the implementation table.
Mappings cover only the hypotheses and clauses they state.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `scale:lem:neumann` (line 696) | Positive-support word finiteness |
| Lemma | `scale:lem:evaluation` (line 721) | Finite-generator evaluation |
| Theorem | `scale:thm:tree` (line 830) | Weighted tree interpolation |
| Theorem | `scale:thm:existence` (line 938) | Uniform infinitesimal normalization |
| Corollary | `scale:cor:gauge` (line 1011) | Untitled |
| Lemma | `scale:lem:secant` (line 1065) | Exact secant identity |
| Theorem | `scale:thm:sharp` (line 1103) | Sharp nonlinear tree-gap law |
| Theorem | `scale:thm:coeffgain` (line 1172) | Coefficientwise gain |
| Corollary | `scale:cor:remainder` (line 1220) | Finite-degree precision certificate |
| Theorem | `scale:thm:bottleneck` (line 1243) | Bottleneck replacement formula |
| Theorem | `scale:thm:chain` (line 1326) | Additive attenuation along the chain |
| Proposition | `scale:prop:global` (line 1486) | Positive scaling over real closed fields |
| Proposition | `scale:prop:cutbound` (line 1539) | A finite cut bound |
| Corollary | `scale:cor:positivebranch` (line 1576) | The positive normalization is the local branch |
| Theorem | `scale:thm:linear` (line 1615) | Basis-gap normalization |
| Corollary | `scale:cor:descent` (line 1678) | Exact local support-group descent |

### surcomplex-field-automorphisms

Source: [surcomplex/surcomplex-field-automorphisms/article.tex](surcomplex/surcomplex-field-automorphisms/article.tex).

Newly placed text; assembly, proof review and formalization remain pending.
Statements are **pending unless explicitly mapped** in the implementation table.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:order` (line 238) | Untitled |
| Theorem | `thm:axis` (line 249) | Centralizer and stabilizer |
| Theorem | `thm:norm` (line 296) | Exact norm rigidity |
| Theorem | `thm:circle` (line 319) | Untitled |
| Lemma | `lem:support` (line 401) | Support control used below |
| Theorem | `thm:monomial` (line 435) | Monomial construction |
| Theorem | `thm:phase` (line 530) | A faithful phase action |
| Theorem | `thm:coeffflow` (line 617) | Taylor motion of coefficient constants |
| Theorem | `thm:shiftflow` (line 685) | A fixed-shift flow |
| Theorem | `thm:decomp` (line 757) | Four layers for surcomplex valued automorphisms |
| Proposition | `prop:continuous` (line 899) | Untitled |
| Proposition | `prop:discrete` (line 930) | Untitled |
| Theorem | `thm:derivative` (line 1014) | Derivative dichotomy for field automorphisms |
| Theorem | `thm:zeroderiv` (line 1034) | Exponent dilations have derivative zero |
| Corollary | `cor:bidifferentiable` (line 1064) | Untitled |
| Theorem | `thm:acfhomogeneity` (line 1096) | Class back-and-forth |
| Theorem | `thm:orderedhomogeneity` (line 1123) | Ordered surreal extension |
| Proposition | `prop:nondefinability` (line 1165) | Untitled |
| Proposition | `prop:fixedfields` (line 1204) | Untitled |
| Theorem | `thm:torsion` (line 1265) | Finite subgroups and real forms |
| Theorem | `thm:inequivalentrealform` (line 1297) | Untitled |
| Lemma | `lem:displacement` (line 1396) | Displacement cannot be globally bounded |
| Theorem | `thm:expfaithful` (line 1419) | Faithful value-group action |
| Proposition | `prop:rationalnonlift` (line 1471) | Untitled |
| Theorem | `thm:L` (line 1507) | Logarithmic-modulus automorphisms |
| Proposition | `prop:conjugacycriterion` (line 1895) | Untitled |

### euclidean-three-space

Source: [surreal/euclidean-three-space/article.tex](surreal/euclidean-three-space/article.tex).

Newly placed text; assembly, proof review and formalization remain pending.
Statements are **pending unless explicitly mapped** in the implementation table.

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:phase` (line 309) | Every direction has a finite phase |
| Theorem | `thm:vector` (line 375) | Euclidean vector identities over the scalar field |
| Theorem | `thm:skew` (line 507) | Distance and closest points of nonparallel lines |
| Theorem | `thm:isometries` (line 618) | Classification of field-distance isometries |
| Theorem | `thm:rodrigues` (line 651) | Rodrigues formula |
| Theorem | `thm:angularmetric` (line 858) | Angular triangle inequality |
| Theorem | `thm:spherical-laws` (line 967) | Spherical sine and cosine laws |
| Theorem | `thm:polar` (line 1010) | Polar duality |
| Theorem | `thm:SSS` (line 1085) | Complete side-data criterion and reconstruction |
| Proposition | `prop:SSA` (line 1169) | Exact SSA alternatives |
| Theorem | `thm:ceva` (line 1287) | Spherical Ceva |
| Theorem | `thm:excess` (line 1320) | Branch-correct spherical excess |
| Theorem | `thm:polygonarea` (line 1400) | Consistency, positivity, and finite additivity |
| Theorem | `thm:holonomy` (line 1581) | Holonomy equals spherical excess |
| Theorem | `thm:local-area` (line 1687) | Uniform gnomonic area comparison |
| Proposition | `prop:conditioning` (line 1759) | Three conditioning estimates |

### finite-surreal-probability

Source: [surreal/finite-surreal-probability/article.tex](surreal/finite-surreal-probability/article.tex).

Newly placed text; assembly, proof review and formalization remain pending.
Statements are **pending unless explicitly mapped** in the implementation table.

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:workspace` (line 244) | Local exponential workspace |
| Proposition | `prop:st` (line 271) | Residue algebra |
| Theorem | `thm:finitebounds` (line 407) | Variance, Cauchy--Schwarz, and tail bounds |
| Theorem | `thm:skeleton` (line 531) | Conditional leading-scale skeleton |
| Theorem | `thm:compression` (line 568) | Signed-row lexicographic compression |
| Theorem | `thm:scalebayes` (line 620) | Minimum-plus Bayes with coefficient tie breaking |
| Theorem | `thm:stability` (line 681) | Absolute and valuation-sensitive conditioning stability |
| Proposition | Line 750 (unlabeled) | Logit coordinates |
| Proposition | `prop:softbound` (line 831) | Normalization and perturbation bounds |
| Theorem | `thm:multisoft` (line 861) | Finite multiscale softmax limit |
| Theorem | `thm:kl` (line 916) | Finite Gibbs inequality and entropy bounds |
| Theorem | `thm:dataprocessing` (line 984) | Finite data processing |
| Theorem | `thm:gibbs` (line 1070) | Surreal finite Gibbs principle |
| Proposition | `prop:separation` (line 1144) | No attained logistic optimum under strict separation |
| Proposition | Line 1201 (unlabeled) | Bounded finite-horizon optional stopping |
| Proposition | `prop:fine` (line 1256) | Set-indexed fine convergence is eventually constant |
| Theorem | `thm:hierarchy` (line 1352) | Normalized hierarchy of real probability laws |
| Theorem | `thm:integrationfailure` (line 1469) | An uncountable-support positivity failure |
| Theorem | `thm:rarecoin` (line 1583) | A repeated infinitesimal success probability |
| Theorem | `thm:faircoin` (line 1609) | A repeated infinitesimal perturbation of a fair coin |
| Lemma | `lem:embedding` (line 1663) | Set-sized relative field embedding |
| Theorem | `thm:extension` (line 1768) | All-subsets regular extension after field enlargement |
| Corollary | `cor:coinextension` (line 1812) | The two coin models do have regular finite-additive laws |
| Proposition | `prop:tailfailure` (line 1885) | Finite-update shadows need not recover rare tail conditioning |
| Theorem | `thm:shadowcountable` (line 1933) | A continuity test for the shadow |

### vector-and-tensor-fields

Source: [surreal/vector-and-tensor-fields/article.tex](surreal/vector-and-tensor-fields/article.tex).

Newly placed text; assembly, proof review and formalization remain pending.
Statements are **pending unless explicitly mapped** in the implementation table.

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `prop:localize` (line 205) | Localization of set-sized scalar data |
| Lemma | `lem:neumann` (line 248) | Classical support lemma |
| Corollary | `cor:geometric` (line 267) | Geometric inversion |
| Proposition | `prop:diffalgebra` (line 384) | Differential algebra |
| Theorem | `thm:prolongation` (line 507) | Multivariable smooth prolongation |
| Proposition | `prop:diffeo` (line 605) | Lifting coordinate diffeomorphisms |
| Theorem | Line 784 (unlabeled) | Levi--Civita construction in the admissible algebra |
| Proposition | Line 866 (unlabeled) | Bianchi identities and conservation |
| Theorem | `thm:stokes` (line 1026) | Hahn Stokes theorem |
| Proposition | Line 1049 (unlabeled) | Positivity for smooth common-support integrands |
| Theorem | `thm:poincare` (line 1078) | Support-preserving local exactness |
| Theorem | `thm:derham` (line 1144) | Compact de Rham base change |
| Corollary | `cor:hodge` (line 1190) | Coefficientwise Hodge decomposition |
| Theorem | `thm:reduction` (line 1234) | Regular reduction of tensor geometry |
| Proposition | `prop:threshold` (line 1261) | A quantitative support threshold |
| Theorem | `thm:flow` (line 1387) | Near-real Hahn flows |
| Theorem | `thm:lifting` (line 1475) | Regular nonlinear Hahn lifting |
