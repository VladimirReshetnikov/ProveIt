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

The [document map](README.md) identifies fifteen main reports. The index below
records every literal `theorem`, `lemma`, `proposition`, and `corollary`
environment in those reports. Counts are a navigation aid, **not a completeness
certificate**: examples, equations, prose assertions, short proofs, and archived
manuscripts also contain mathematical claims. The foundations README's count of
30 theorem-environment results includes six examples and a design principle;
the narrower inventory here counts its 23 theorem/lemma/proposition/corollary
statements.

There are also **33 preserved source manuscripts** under `sources/`. Their
893 literal standard result environments are not 893 additional independent
results: merged reports deliberately overlap them, and some change scope or
resolve conflicting definitions. A complete coverage audit must map each source
claim to an equivalent main-report statement, a separate proof obligation, or
a documented mathematical correction. No such equivalence is presumed here.
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

## Implementation mappings

The mapped modules pass `lake build`, including the default `SurrealAudit`
target. The audit checks every imported `Surreal` declaration and rejects any
transitive axiom beyond `propext`, `Quot.sound`, and `Classical.choice`. All ten
size-obstruction theorems have no axiom dependencies. This establishes the
listed Lean statements, not the outstanding surreal interpretation. Every
main-report statement not fully covered below remains pending, including
remaining clauses of a partially mapped statement.

| Source obligation | Lean declarations | Scope of current implementation |
|---|---|---|
| `found:prop:allcuts` | `Surreal.Foundations.noUniversalStrictBound`, `noUnrestrictedStrictBounds`, `noUnrestrictedUpperBounds`, `noUnrestrictedCuts` in [SizeObstructions.lean](../Surreal/Foundations/SizeObstructions.lean) | Full unrestricted-bound and two-sided-cut contradiction for an arbitrary irreflexive relation. **Proved**; integrated build and axiom audit pass. |
| `found:sub:cutdata` | `Surreal.Foundations.SmallCutData`, `SmallCutData.IsRealizedBy`, `HasSmallCutFillers`, `HasSmallStrictUpperBounds` | Size-aware data and explicit properties, with no asserted inhabitant of the cut-filler property. |
| `found:lem:bounds` | `Surreal.Foundations.HasSmallCutFillers.hasSmallStrictUpperBounds`, `HasSmallCutFillers.exists_strict_lower_bound`, `HasSmallCutFillers.exists_strict_lower_bound_above`, `HasSmallStrictUpperBounds.exists_bound_of_small_set` | Upper/lower/positive-lower bounds conditional on a proved small-cut-filler property. Constructing that property for a surreal carrier remains pending. |
| `found:prop:universecut` | `Surreal.Foundations.not_small_of_small_strict_upper_bounds`, `not_small_of_small_cut_fillers` | The abstract non-smallness implication using Mathlib `Small`. The particular surreal universe interpretation remains pending. |
| `found:eq:pairmul`, `found:eq:conj`, `found:eq:pairinv`; part of `found:prop:complex` | `Surreal.Complexify`, `Complexify.mul_re`, `mul_im`, `I_sq`, `conj_conj`, `conj_mul`, `noRootNegOne`, `inv_eq`, `inv_re`, `inv_im` in [Complexify.lean](../Surreal/Algebra/Complexify.lean) | Mathlib quadratic algebra and its field instance over an arbitrary ordered field. Algebraic closedness and the class-coded surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `found:eq:gram`, `found:eq:cauchyschwarz`, `trigonometry:eq:gram` | `Surreal.Complexify.gram_identity`, `cauchy_schwarz_sq`, `normSq_mul`, `mul_conj` | Generic algebraic identities and their ordered-field consequence. The scalar formula is proved independently of any surreal representation. **Prerequisites proved**; build and axiom audit pass. |
| `a:prop:triangle` | `Surreal.Complexify.modulus_mul`, `modulus_add_le`, `abs_re_le_modulus`, `abs_im_le_modulus`, `inv_eq_modulus` in [Modulus.lean](../Surreal/Algebra/Modulus.lean) | The stated identities over an arbitrary real closed ordered field, with modulus valued in that field. The concrete surcomplex interpretation remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `found:eq:rationalcircle`; affine clauses of `trigonometry:thm:cayley` | `Surreal.Complexify.normSq_circleParam`, `circleParam_ne_neg_one`, `circleCoord_circleParam`, `circleParam_circleCoord`, `circleParam_injective`, `circleEquiv` in [Circle.lean](../Surreal/Algebra/Circle.lean) | The rational affine chart and its inverse give an equivalence over any ordered field. The projective extension and direction multiplication are mapped below. The half-angle identity and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Projective and algebraic multiplication clauses of `trigonometry:thm:cayley`, `trigonometry:eq:cayley`, `trigonometry:eq:projectiveaddition` | `Surreal.Complexify.projectiveCircleEquiv`, `projectiveCircleEquiv_mk`, `circleParam_eq_fraction`, `projective_add_pair_ne_zero`, `projectiveAdd_mk`, `circleParam_mul`, `circleParam_mul_eq_neg_one_iff`, `projectiveAdd_infty_infty` in [ProjectiveCircle.lean](../Surreal/Algebra/ProjectiveCircle.lean) | Mathlib's actual projectivization of `Fin 2 → F` is equivalent to the norm-square-one circle over any ordered field. The chart has the homogeneous quotient formula and transports direction multiplication to `[ps+qr:qs-pr]`, whose output pair is proved nonzero. The affine rule applies exactly off its zero denominator; zero denominator gives `-1`, and two points at infinity give affine zero. Associativity and commutativity are also proved. The tangent/half-angle relation, infinitesimal proximity claim and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Factorization clauses of `polynomial:thm:fta`, `polynomial:eq:factorization`, `polynomial:eq:logderivative` | `Surreal.FinitePolynomial.exists_root`, `factorization`, `factorization_grouped`, `exists_unique_factorization`, `factorization_unique`, `sum_rootMultiplicities`, `logarithmic_derivative`, `logarithmic_derivative_grouped` in [Polynomial.lean](../Surreal/Algebra/Polynomial.lean) | Root existence, unique scalar/multiset factorization, grouped multiplicities and both logarithmic-derivative formulas. Existence assumes algebraic closedness; uniqueness holds over every field. The rational identities require a nonroot evaluation point. The concrete surreal/Hahn workspace construction remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Division, gcd and ideal clauses of `polynomial:thm:fta`; gcd formula in `polynomial:eq:logderivative` | `Surreal.FinitePolynomial.exists_unique_division`, `exists_monic_gcd`, `gcd_bezout`, `ideal_principal`, `ideal_pair_eq_span_gcd`, `squarefree_iff_gcd_derivative_eq_one`, `gcd_derivative_rootMultiplicity`, `gcd_derivative_eq_prod` in [PolynomialDivision.lean](../Surreal/Algebra/PolynomialDivision.lean) | Unique division, normalized monic Bézout gcds and principal ideals over every field. The squarefree criterion assumes perfectness (supplied by characteristic zero); derivative multiplicities use characteristic zero. The grouped gcd product assumes a nonzero split polynomial and does not need monicity of the input. **Prerequisites proved**; build and axiom audit pass. |
| Multiplicity and Taylor clauses of `polynomial:thm:fta` | `Surreal.FinitePolynomial.multiplicity_eq_iff_derivatives`, `multiplicity_isLeast_nonzero_derivative`, `derivative_rootMultiplicity`, `multiple_root_iff`, `taylor_coeff_eq_derivative`, `taylor_eq_sum_derivatives`, `eq_sum_derivatives`, `eval_add_eq_sum_derivatives` in [PolynomialMultiplicity.lean](../Surreal/Algebra/PolynomialMultiplicity.lean) | The least nonvanishing derivative, derivative multiplicity and finite Taylor formulas over characteristic-zero fields. The least-index characterization explicitly excludes the zero polynomial. **Prerequisites proved**; build and axiom audit pass. |
| Local kernel calculation for `polynomial:thm:crt` | `Surreal.FinitePolynomial.pow_linear_dvd_iff_derivatives_vanish`, `derivative_jets_eq_iff_dvd_sub` | A jet vanishes exactly when the corresponding power of `X - a` divides the polynomial; equal jets correspond to divisibility of the difference. These include zero polynomials. **Prerequisites proved**; build and axiom audit pass. |
| Hermite interpolation clause of `polynomial:thm:crt` | `Surreal.FinitePolynomial.exists_unique_interpolation_representative`, `exists_unique_hermite_interpolant`, `exists_unique_hermite_interpolant_fin` in [PolynomialInterpolation.lean](../Surreal/Algebra/PolynomialInterpolation.lean) | Arbitrary finite derivative jets at distinct nodes determine a unique polynomial of degree below the sum of multiplicities, over a characteristic-zero field. Zero multiplicities and the empty index type are included. Other finite CRT clauses are mapped separately below. **Prerequisites proved**; build and axiom audit pass. |
| Quotient and idempotent clauses of `polynomial:thm:crt`, `polynomial:eq:finiteCRT` | `Surreal.FinitePolynomial.polynomialCRT`, `polynomialCRT_mk_derivative_jet`, `crtIdempotent`, `mk_eq_crtIdempotent_of_local_congruences`, `exists_crtIdempotent_representative`, `crtIdempotent_mul_self`, `crtIdempotent_mul_of_ne`, `sum_crtIdempotent` in [PolynomialCRT.lean](../Surreal/Algebra/PolynomialCRT.lean) | The quotient by the product of local moduli is ring-isomorphic to the product of truncated polynomial rings. Its Taylor forward map has the displayed derivative-jet formula in characteristic zero. Coordinate idempotents are orthogonal and sum to one, with bounded-degree representatives and a local-congruence criterion. Empty indices and zero multiplicities are included. Concrete representatives and the simple-root formula are mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Explicit local inverse and `PᵢCᵢ` representatives in `polynomial:thm:crt` | `Surreal.FinitePolynomial.inverseJet`, `inverseJet_eq_sum`, `node_pow_dvd_mul_inverseJet_sub_one`, `inverseJet_unique`, `interpolationCofactor_eq_div`, `interpolationCofactor_eval_ne_zero`, `inverseJetIdempotentPolynomial_degree_lt`, `mk_inverseJetIdempotentPolynomial` in [PolynomialInverseJet.lean](../Surreal/Algebra/PolynomialInverseJet.lean) | Truncating the actual reciprocal formal Taylor series gives the unique local inverse of degree below the multiplicity. The cofactor is exactly `P / Aᵢ` and is nonzero at its node. Each product `PᵢCᵢ` has degree below the total multiplicity, satisfies all local congruences, and represents the coordinate idempotent. Works over every field, including zero multiplicities. The derivative formula is mapped below. **Prerequisites proved**; build and axiom audit pass. |
| Constructive interpolant in the proof of `polynomial:thm:crt` | `Surreal.FinitePolynomial.hermiteInterpolant`, `hermiteInterpolant_local_congruences`, `hermiteInterpolant_degree_lt`, `hermiteInterpolant_unique`, `polynomialCRT_hermiteInterpolant`, `polynomialCRT_symm_mk`, `hermiteJetInterpolant_derivative`, `hermiteJetInterpolant_unique` in [PolynomialHermiteFormula.lean](../Surreal/Algebra/PolynomialHermiteFormula.lean) | The remainder modulo `P` of the explicit finite sum `∑ᵢ PᵢCᵢqᵢ` is the unique interpolant below the total-multiplicity degree bound with the prescribed polynomial residue classes. Its image under the CRT equivalence is the translated tuple, and translating local-variable representatives back gives the explicit inverse of that equivalence. Choosing the local Taylor representatives realizes the requested derivative jets in characteristic zero. Empty node sets and zero multiplicities are included. **Prerequisites proved**; build and axiom audit pass. |
| Formal reciprocal derivative formula in `polynomial:eq:inversejet` | `Surreal.FinitePolynomial.constantCoeff_iterate_powerSeries_derivative`, `reciprocalDerivativeNumerator`, `iterate_derivative_inverse_taylor`, `inverseJet_eq_sum_formal_derivatives`, `inverseJet_eq_sum_reciprocal_numerators`, `reciprocal_jet_denominator_ne_zero` in [PolynomialRationalJets.lean](../Surreal/Algebra/PolynomialRationalJets.lean) | In characteristic zero, the inverse jet coefficients are the iterated derivatives of the reciprocal Taylor series at zero divided by factorials. The repeated quotient-rule numerator recurrence is verified using Mathlib's actual formal derivative, yielding explicit coefficients `Nⱼ(a)/(q(a)^(j+1)·j!)` with nonzero denominators when `q(a) ≠ 0`. This is an algebraic local formal-series interpretation; a global `RatFunc` derivative operator and comparison with analytic derivatives are not supplied. **Prerequisites proved**; build and axiom audit pass. |
| Simple-root clause of `polynomial:thm:crt`, `polynomial:eq:lagrange` | `Surreal.FinitePolynomial.lagrange_formula`, `nodal_derivative_eval`, `nodal_derivative_eval_ne_zero`, `eval_lagrange_formula`, `lagrange_denominator_ne_zero` in [PolynomialLagrange.lean](../Surreal/Algebra/PolynomialLagrange.lean) | The displayed Lagrange polynomial identity reuses Mathlib's nodal polynomial and exact division by its selected linear factor. The scalar rational formula is proved away from the nodes, with every denominator nonzero. Valid over any field, without a lower bound on node separation; the degree hypothesis also handles an empty node set. Surcomplex specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Viète coefficient identity preceding `polynomial:eq:newton1`; `polynomial:eq:newton1`, `polynomial:eq:newton2` | `Surreal.FinitePolynomial.rootPowerSum`, `vieta_prod_coefficient`, `vieta_coefficient`, `newton_multiset_uniform`, `newton_identity_le_degree`, `newton_identity_gt_degree` in [PolynomialNewton.lean](../Surreal/Algebra/PolynomialNewton.lean) | The coefficient and both Newton identities are proved for monic split polynomials with roots counted as a multiset. The first regime requires `0 < k ≤ n`; the second includes degree-zero polynomials. Generic finite multiset identities hold over every commutative ring, and the field specializations impose no characteristic-zero assumption. Uses Mathlib's universal symmetric-polynomial identities with finite evaluation. Surcomplex specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:resultantproduct` and surrounding determinant, specialization, interchange-sign and common-root assertions | `Surreal.FinitePolynomial.resultant_eq_leadingCoeff_mul_prod_eval`, `resultant_eq_leadingCoeffs_mul_prod_sub`, `resultant_swap`, `resultant_eq_sylvester_det`, `sylvester_eq_matrix_bezout`, `resultant_map_fixed_degrees`, `resultant_map_of_injective`, `resultant_eq_zero_iff_common_root`, `sylvester_has_kernel_iff_common_root`, `resultant_ne_zero_iff_isCoprime` in [PolynomialResultant.lean](../Surreal/Algebra/PolynomialResultant.lean) | Mathlib's resultant at the actual degrees has the root products with both leading-coefficient powers and the Sylvester determinant interpretation. Arbitrary coefficient maps preserve a fixed-size determinant; injectivity additionally preserves actual degrees. The common-root criterion assumes the first polynomial is nonzero and split, and permits a zero second polynomial. The finite Bézout map is identified with the Sylvester matrix in explicit bases, and a nonzero kernel vector characterizes common roots. Coprimality requires no splitting. Native `Res(0,0)=1` is documented. Discriminants and Hahn valuation identities are mapped separately below. Quotient multiplication determinants and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:discdef` and its repeated-root assertion | `Surreal.FinitePolynomial.leadingCoeff_mul_discr_eq_sign_mul_resultant`, `discr_eq_sign_mul_resultant`, `discr_ne_zero_iff_squarefree`, `discr_eq_zero_iff_repeated_root`, `discr_C_mul_prod_X_sub_C`, `discr_prod_X_sub_C`, `discr_eq_leadingCoeff_pow_mul_prod_sub_sq` in [PolynomialDiscriminant.lean](../Surreal/Algebra/PolynomialDiscriminant.lean) | Uses Mathlib's native discriminant and actual-degree resultant in characteristic zero. The squared root-difference formula includes the leading-coefficient power and counts repeated root occurrences. Positive degree guards the general formula; monic constants and native discriminant-one conventions are included. The squarefree criterion needs no splitting, while the repeated-root criterion assumes a nonzero split polynomial. Valuation identities are mapped separately; quotient trace-pairing discriminants and surreal specialization remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:prop:rootbounds`, `polynomial:eq:cauchybound` | `Surreal.FinitePolynomial.root_lt_cauchy_bound`, `reciprocal_cauchy_bound_lt_root`, `root_le_two_mul_radialCoefficientMax`, `root_eq_zero_of_radialCoefficientMax_eq_zero`; `Surreal.Complexify.modulus_root_lt_cauchy_bound`, `reciprocal_cauchy_bound_lt_modulus_root`, `modulus_root_le_two_mul_radialCoefficientMax` in [PolynomialRootBounds.lean](../Surreal/Algebra/PolynomialRootBounds.lean) | Both strict Cauchy bounds use the exact finite maxima in the source, with a nonzero constant coefficient for the lower bound. The radial maximum uses nonnegative `(n-j)`th roots in a real closed ordered base field and proves the non-strict bound `2M`, including the zero-maximum conclusion. The abstract proofs use an ordered-field-valued absolute value, specialized to the existing base-field modulus of `Complexify F`; no Archimedean assumption or real-valued norm is introduced. Positive degree makes all maxima nonempty. Surreal specialization remains pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:resval` and the nodal derivative separation sum defining `dᵢ` | `Surreal.HahnSeries.orderTop_resultant_eq_sum_eval`, `orderTop_resultant`, `order_resultant`, `orderTop_nodal_derivative_eval`, `order_nodal_derivative_eval` in [PolynomialValuation.lean](../Surreal/HahnSeries/PolynomialValuation.lean) | Resultant valuations retain the leading-coefficient powers and every root-pair occurrence. The formulas with `orderTop` retain infinity when products vanish; exponent-group-valued `order` formulas require nonzero polynomials/resultant or injective nodes. Splitting is explicit, and no Hahn algebraic closedness or surreal embedding is assumed. **Prerequisites proved**; build and axiom audit pass. |
| `trigonometry:eq:dotcross`, `trigonometry:eq:gram` and following triangle-equality characterization | `Surreal.Complexify.dot`, `cross`, `dot_sq_add_cross_sq`, `abs_dot_le`, `modulus_add_eq_iff_dot`, `modulus_add_eq_iff_pos_quotient` in [Geometry.lean](../Surreal/Algebra/Geometry.lean) | Coordinate identities and the equality criterion for nonzero vectors over any real closed ordered field. The positive quotient is an embedded element of that same base field. **Prerequisites proved**; build and axiom audit pass. |
| Area clause of `trigonometry:thm:heron`, factorization behind `trigonometry:eq:heronfactor` | `Surreal.Complexify.heron_factorization`, `heron`, `triangleArea` | Heron's identity for the triangle with vertices `0,z,w`, including degenerate cases. Radius, incenter, bisector and half-angle clauses remain pending, as does surreal specialization. **Prerequisites proved**; build and axiom audit pass. |
| Inequality clause of `trigonometry:thm:ptolemy` | `Surreal.Complexify.ptolemy_identity`, `ptolemy` | The four-point inequality over any real closed ordered base field. Cyclic order and the cyclic equality case remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Root-persistence clause of `found:thm:workspace` | `Surreal.FinitePolynomial.roots_map`, `root_mem_range`, `roots_map_of_isAlgClosed` | Roots and multiplicities of split polynomials under field extension. Workspace construction, support compatibility and the other localization clauses remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Coefficientwise complexification in the proof of `polynomial:prop:workspace` | `Surreal.HahnSeries.complexifyHahnEquiv`, `coeff_complexifyToHahn`, `coeff_hahnToComplexify_re`, `coeff_hahnToComplexify_im`, `support_complexifyToHahn` in [HahnSeries/Complexify.lean](../Surreal/HahnSeries/Complexify.lean) | A ring equivalence between the quadratic extension of Hahn series over `R` and Hahn series with coefficients in `R[i]`, for any commutative ring `R`. Real and imaginary projection supports are contained in the original support, and the combined support is exactly their union. Native coefficient and conjugation results are mapped below. Closure and surreal workspace construction remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `K_Γ = F_Γ[i]` and conjugation-fixed-field identification in `polynomial:prop:workspace` | `Surreal.Complexify.complexEquiv` in [Algebra/ComplexNumbers.lean](../Surreal/Algebra/ComplexNumbers.lean); `Surreal.HahnSeries.conjugation_eq_self_iff_mem_range` in [Conjugation.lean](../Surreal/HahnSeries/Conjugation.lean); `realComplexHahnEquiv`, `complexConjugation_realComplexHahnEquiv`, `complexConjugation_eq_self_iff_mem_range`, `orderTop_complexConjugation`, `realHahnSubfieldEquiv`, `mem_realHahnSubfield_iff` in [HahnSeries/ComplexNumbers.lean](../Surreal/HahnSeries/ComplexNumbers.lean) | The quadratic algebra over native `ℝ` is ring-isomorphic to native `ℂ`, compatibly with scalar inclusion, `i`, and conjugation. Thus complex Hahn series are the quadratic extension of real Hahn series; the conjugation-fixed elements are precisely the injectively embedded real Hahn series. Conjugation preserves support and Hahn order. The generic fixed-image theorem assumes a characteristic-zero coefficient field; the ring statements allow ordered cancellative exponent monoids. For exponent groups, the real image is a bundled subfield, isomorphic to the real Hahn field and characterized by conjugation fixedness. Real/algebraic closedness and the actual surreal embedding remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Image-containment clause of `found:thm:finitepoints` | `Surreal.FinitePolynomial.finite_algebra_character_descends` | A character of a finite algebra over an algebraically closed base takes values in that base. Local decomposition and base-change/local-length assertions remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `a:lem:neumann`, `a:rule:wordlength` | `Surreal.HahnSeries.neumann_add`, `finite_words_of_sum_eq`, `finite_nondecreasing_words_of_sum_eq`, `neumann_positive` in [Neumann.lean](../Surreal/HahnSeries/Neumann.lean) | **Proved** over an arbitrary ordered abelian group: well-ordered sumsets, finite pair-sum fibers, a well-ordered positive generated monoid, and finite fixed-sum word fibers across all lengths. The all-word version strengthens the requested nondecreasing-word statement. Uses Mathlib's partial well-order and Higman APIs. |
| Constant-family specialization of `a:def:summable`, `a:rule:clauseii`; nonsummability part of `a:ex:notsummable` | `Surreal.HahnSeries.summable_constants_iff`, `hsum_constants`, `not_summable_constants_of_infinite`, `not_summable_geometric_constants` in [Constants.lean](../Surreal/HahnSeries/Constants.lean) | A family of constants is strongly summable exactly when its coefficient function has finite support. The nonzero constants `2⁻ⁿ` give a counterexample even though their support union is contained in `{0}`. Uses Mathlib's actual `SummableFamily`; ordinary analytic convergence and surreal interpretation are separate obligations. **Prerequisites proved**; build and axiom audit pass. |
| Regrouping and interchange assertions following `a:def:summable` | `Surreal.HahnSeries.restrict`, `regroup`, `coeff_hsum_fiber`, `coeff_regroup`, `hsum_regroup`, `hsum_fubini` in [Regroup.lean](../Surreal/HahnSeries/Regroup.lean) | Any index map regroups a jointly summable Hahn family into a summable family of fiber sums with unchanged total. Includes infinite fibers and double-sum interchange, with joint summability explicit throughout. Uses finite coefficient families rather than a topological convergence operation. The surreal interpretation remains pending. **Prerequisites proved**; build and axiom audit pass. |
| Algebraic standard-part claims in `a:eq:st` and the following decomposition | `Surreal.HahnSeries.nonnegativeSubring`, `standardPart`, `standardPart_surjective`, `mem_infinitesimalIdeal`, `infinitesimalIdeal_isMaximal`, `residueEquiv`, `exists_unique_standardPart_decomposition` in [StandardPart.lean](../Surreal/HahnSeries/StandardPart.lean) | On the nonnegative-order Hahn subring over a coefficient field, coefficient-zero extraction is a surjective ring homomorphism with maximal positive-order kernel. The quotient is the coefficient field, and the constant-plus-positive-order decomposition is unique. Zero has order infinity and is included. Identification with ordinary modulus-bounded surcomplex elements and the surreal bridge remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `polynomial:eq:reductionfactor` and its preceding root/coefficient assertions | `Surreal.HahnSeries.orderTop_nonneg_of_monic_root`, `orderTop_nonneg_of_monic_root_of_coeff_nonneg`, `coeff_orderTop_nonneg_of_monic_split_roots`, `coeff_orderTop_nonneg_multiset_prod`, `splits_nonnegative_of_splits`, `standardPart_factorization`, `roots_standardPart` in [PolynomialReduction.lean](../Surreal/HahnSeries/PolynomialReduction.lean) | Roots of monic polynomials with nonnegative-order coefficients have nonnegative order. The converse holds for split monic polynomials, including finite products. A monic polynomial over the nonnegative-order subring that splits in the Hahn field already splits in the subring. Standard part preserves the complete linear factorization and maps the root multiset, adding multiplicities when reductions coincide. Splitting is explicit; Hahn algebraic closedness and identification with surreal modulus-boundedness remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Univariate summability and ring-compatibility clauses of `a:cor:complexsub` | `Surreal.HahnSeries.evaluate`, `evaluate_X`, `summable_coeff_mul_powers`, `coeff_evaluate`, `coeff_zero_evaluate`, `summable_powers` in [Evaluation.lean](../Surreal/HahnSeries/Evaluation.lean) | Admissible evaluation reuses Mathlib `PowerSeries.heval` as an algebra homomorphism, with an explicit positive-`orderTop` proof and the actual coefficient-times-power term formula. Zero is included because its `orderTop` is infinity. Univariate composition is mapped separately below. Multivariable evaluation, differentiation and the surreal bridge remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Univariate composition clause of `a:cor:complexsub` | `Surreal.HahnSeries.orderTop_evaluate_nonneg`, `orderTop_evaluate_pos_of_constantCoeff_zero`, `coeff_evaluate_eq_sum`, `evaluate_subst` in [Composition.lean](../Surreal/HahnSeries/Composition.lean) | Evaluation of arbitrary formal power series commutes with formal substitution when the inner series has zero constant coefficient and the Hahn argument has positive order. The evaluated inner series is itself proved admissible. Coefficientwise finite-support calculations justify the interchange, including zero inner series or argument. This is generic univariate Hahn composition; multivariable composition, analytic coefficient rings and the surreal interpretation remain pending. **Prerequisites proved**; build and axiom audit pass. |
| `a:eq:geom` and formal remainder in `a:ex:geometric` | `Surreal.HahnSeries.geometric_mul`, `geometric_hsum`, `geometric_remainder` | The strongly summable power family has sum `(1-x)⁻¹`, with exact finite-sum remainder `x^(N+1)/(1-x)`, when `x` has positive order. The identity is generic Hahn algebra. The valuation calculation at the named surreal scale and nonconvergence in the fine topology remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Binomial specialization of `a:cor:complexsub`; root identity used in `b:ramification` and local trigonometric binomial expansions | `Surreal.HahnSeries.binomialTerms_apply`, `binomialPower_eq_hsum`, `orderTop_binomialPower_sub_one_pos`, `binomialPower_add`, `binomialPower_nat`, `binomialPower_rat_root`, `binomialPower_half_sq` in [Binomial.lean](../Surreal/HahnSeries/Binomial.lean); `pow_injective_near_one`, `binomialPower_rat_root_unique`, `exists_unique_root_near_one` in [BinomialRoots.lean](../Surreal/HahnSeries/BinomialRoots.lean) | The proof-gated binomial family has the actual terms `choose r n • x^n`, constant coefficient one, positive-order difference from one, and formal exponent-addition/natural-power laws. Rational exponents give an `m`th root of `1+x` for nonzero natural `m`. Over a characteristic-zero Hahn field, this is the unique root whose difference from one has positive order, using the geometric factor's nonzero standard part `m`. The positive ordered-root identification is mapped below. Ramification normal forms, analytic convergence and the surreal interpretation remain pending. **Prerequisites proved**; build and axiom audit pass. |
| Positive square-root branch in the local trigonometric binomial expansions | `Surreal.HahnSeries.lex_pos_of_sub_one_orderTop_pos`, `binomialPower_lex_pos`, `binomialPower_half_eq_of_nonneg_sq`, `exists_unique_nonneg_sqrt_one_add` in [BinomialOrder.lean](../Surreal/HahnSeries/BinomialOrder.lean) | Over any ordered coefficient field, every rational binomial power near one is positive in Mathlib's lexicographic Hahn order. The half-power is the unique nonnegative square root of `1+x` when `x` has positive order, including zero `x`. The constructed local root needs no real-closedness assumption. Global square-root operations, analytic convergence and the surreal bridge remain pending. **Prerequisites proved**; build and axiom audit pass. |

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
   sums. Then prove `found:thm:workspace`. The six surreal reports branch here:
   graph results need game representations; birthday and broadcast results
   need sign/ordinal arithmetic; evaluation and genetic-gap results need their
   specified supports or differentiation semantics. The plan's two tracks allow
   local Hahn mathematics to proceed before this bridge is finished.
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

`T`, `L`, `P`, `C` mean theorem, lemma, proposition and corollary environments.
Paths below identify the canonical main text, including the two reports whose
source is not named `article.tex`.

| Main report source | T | L | P | C | Total |
|---|---:|---:|---:|---:|---:|
| [foundations-and-computation/computer-algebra/article.tex](foundations-and-computation/computer-algebra/article.tex) | 4 | 0 | 8 | 2 | 14 |
| [foundations-and-computation/foundations/article.tex](foundations-and-computation/foundations/article.tex) | 3 | 2 | 16 | 2 | 23 |
| [surcomplex/analysis/article.tex](surcomplex/analysis/article.tex) | 57 | 10 | 24 | 26 | 117 |
| [surcomplex/analytic-geometry/article.tex](surcomplex/analytic-geometry/article.tex) | 27 | 9 | 9 | 8 | 53 |
| [surcomplex/contours-and-stokes/article.tex](surcomplex/contours-and-stokes/article.tex) | 20 | 4 | 10 | 1 | 35 |
| [surcomplex/finite-deformations/article.tex](surcomplex/finite-deformations/article.tex) | 23 | 10 | 6 | 13 | 52 |
| [surcomplex/global-divisors/article.tex](surcomplex/global-divisors/article.tex) | 11 | 7 | 11 | 8 | 37 |
| [surcomplex/polynomial-algebra/article.tex](surcomplex/polynomial-algebra/article.tex) | 28 | 6 | 9 | 14 | 57 |
| [surcomplex/trigonometry/article.tex](surcomplex/trigonometry/article.tex) | 39 | 4 | 11 | 10 | 64 |
| [surreal/broadcast-sum-of-surreal-sequences/article.tex](surreal/broadcast-sum-of-surreal-sequences/article.tex) | 7 | 8 | 1 | 5 | 21 |
| [surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex](surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex) | 15 | 13 | 7 | 4 | 39 |
| [surreal/genetic-gaps-and-primitives/article.tex](surreal/genetic-gaps-and-primitives/article.tex) | 7 | 3 | 4 | 1 | 15 |
| [surreal/gonshor-laurent-birthdays/article.tex](surreal/gonshor-laurent-birthdays/article.tex) | 5 | 8 | 0 | 5 | 18 |
| [surreal/gonshor-product-birthdays/surreal_product_birthdays.tex](surreal/gonshor-product-birthdays/surreal_product_birthdays.tex) | 3 | 4 | 5 | 2 | 14 |
| [surreal/hahn-evaluation-at-omega/article.tex](surreal/hahn-evaluation-at-omega/article.tex) | 7 | 9 | 5 | 2 | 23 |
| **Total** | 256 | 97 | 126 | 103 | **582** |

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
| Proposition | `cas:prop-countable` (line 557) | The finite-description bound |
| Theorem | `cas:thm-zerotest` (line 607) | Total coefficient access does not decide zero |
| Corollary | `cas:cor-sign` (line 659) | No universal three-way sign; equality reduces to zero testing |
| Corollary | `cas:cor-leading` (line 666) | No universal leading-term algorithm |
| Proposition | `cas:prop-validation` (line 692) | Unrestricted support validation is undecidable |
| Proposition | `cas:prop-leading` (line 712) | A high-rank leading-term and sign obstruction |
| Theorem | `cas:thm-core` (line 1070) | Effective rational monomial core |
| Theorem | `cas:thm-realclosure` (line 1189) | An implementable real-closed and algebraically closed layer |
| Theorem | `cas:thm-grid` (line 1417) | Finite extraction from a positive grid |
| Proposition | `cas:prop-precision` (line 1568) | Basic certified precision rules |
| Proposition | `cas:prop-finiteprefix` (line 1614) | Finite-prefix criterion for rank-one grids |
| Proposition | `cas:prop-lift` (line 2131) | Correctness of infinitesimal substitution |
| Proposition | `cas:prop-periods` (line 3376) | Every global extension acquires an infinite period |
| Proposition | `cas:prop-archimedean` (line 3733) | No order-preserving embedding |

### foundations

Source: [foundations-and-computation/foundations/article.tex](foundations-and-computation/foundations/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `found:prop:proper` (line 642) | There is no set of all surreal numbers |
| Proposition | `found:prop:allcuts` (line 695) | The unrestricted cut axiom is inconsistent |
| Lemma | `found:lem:bounds` (line 726) | Bounds for sets of surreals; the small positive lower bound |
| Proposition | `found:prop:incomplete` (line 771) | Untitled |
| Proposition | `found:prop:scott` (line 912) | Set codes for a definable class quotient |
| Proposition | `found:prop:recursion` (line 1202) | Local recursion and coherent assembly |
| Proposition | `found:prop:universe` (line 1325) | Why universe relativization avoids the cut contradiction |
| Proposition | `found:prop:universecut` (line 1344) | The missing self-cut |
| Proposition | `found:prop:closure` (line 1448) | Closure under a fixed set of finitary operations |
| Proposition | `found:prop:complex` (line 1542) | Finite data complexify safely |
| Theorem | `found:thm:workspace` (line 1690) | Workspace localization |
| Theorem | `found:thm:finitepoints` (line 1859) | Finite algebra over an algebraically closed base |
| Proposition | `found:prop:positive` (line 2025) | Support-local nonlinear recursion |
| Corollary | `found:cor:fixeddomain` (line 2058) | Fixed domain |
| Proposition | `found:ex:rescaling` (line 2182) | Universal rescaling fails in a fixed Hahn field |
| Proposition | `found:prop:rescalingpositive` (line 2210) | The enlarged group repairs it |
| Theorem | `found:thm:discrete` (line 2409) | Small subsets and small-index nets are discrete |
| Proposition | `found:prop:twotopologies` (line 2471) | Intrinsic and full-class subspace topologies differ |
| Lemma | `found:lem:nometric` (line 2510) | No countable ball basis is coinitial |
| Corollary | `found:cor:nopaths` (line 2568) | No nonconstant fine-continuous paths |
| Proposition | `found:prop:period` (line 2815) | Why an infinite period is not a paradox |
| Proposition | `found:prop:signtree` (line 2939) | Sign-tree categoricity |
| Proposition | `found:prop:univalence` (line 3358) | The elementary incompatibility test |

### analysis

Source: [surcomplex/analysis/article.tex](surcomplex/analysis/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `a:prop:triangle` (line 186) | Modulus identities over an ordered field |
| Lemma | `a:lem:valbound` (line 291) | Crude valuation bound |
| Proposition | `a:prop:fragment` (line 358) | Containment of set-sized data |
| Lemma | `a:lem:neumann` (line 682) | Neumann support lemma |
| Corollary | `a:cor:complexsub` (line 723) | No growth condition |
| Theorem | `a:thm:discrete` (line 832) | Set-sized convergence collapses, with a uniform radius |
| Proposition | `a:prop:clopen` (line 876) | Clopen infinitesimal cosets |
| Corollary | `a:cor:nopath` (line 895) | No nonconstant continuous paths |
| Proposition | `b:inclusions` (line 1048) | The inclusions, and what witnesses them |
| Proposition | `b:fivefailures` (line 1118) | Five classical statements fail in the germ-analytic class |
| Proposition | `b:noremoval` (line 1193) | No unrestricted removability theorem |
| Proposition | `b:twistwitness` (line 1222) | The twisted-exponential witness |
| Theorem | `b:nogo` (line 1268) | Contour no-go |
| Corollary | `b:nogo-fundamental` (line 1298) | The fundamental theorem cannot be widened |
| Corollary | `b:log-not-coherent` (line 1307) | $\mathcal L$ is not a coherent primitive of $1/z$ |
| Corollary | `b:primitive-uniqueness-scope` (line 1320) | Uniqueness of primitives is a coherent statement |
| Lemma | `b:blocks` (line 1391) | Separated degree blocks |
| Theorem | `b:realization` (line 1461) | Realization of every formal series |
| Proposition | `b:remainder` (line 1501) | Uniform Taylor remainder |
| Corollary | `b:nogrowth` (line 1527) | No growth condition |
| Proposition | `b:globalseries` (line 1544) | Everywhere-summable means polynomial |
| Theorem | `b:germalgebra` (line 1574) | {The germ algebra is $\K[[X]]$} |
| Corollary | `b:isolated` (line 1638) | Isolated zeros of a germ |
| Theorem | `b:derivation-obstruction` (line 1681) | Derivation obstruction |
| Theorem | `b:CRgerm` (line 1733) | Cauchy--Riemann criterion for germs |
| Theorem | `b:harmonicgerm` (line 1768) | Harmonic conjugate germs |
| Theorem | `b:inverse` (line 1807) | Local inverse and implicit function theorems for germs |
| Theorem | `b:ramification` (line 1845) | Finite ramification normal form |
| Corollary | `b:localopen` (line 1875) | Local openness and no local modulus maximum |
| Corollary | `b:localidentity` (line 1916) | Local identity and maximum-modulus principles |
| Proposition | `b:formalprimitive` (line 1968) | The only local primitive obstruction |
| Theorem | `b:reschange` (line 1985) | Change of variable, with the ramification factor |
| Corollary | `b:localargument` (line 2007) | Local argument principle |
| Proposition | `b:formalres` (line 2016) | Formal residue facts and removability |
| Theorem | `b:lagrange` (line 2051) | Lagrange--B\"urmann inversion |
| Theorem | `c:p4:eval` (line 2262) | Faithful coherent evaluation |
| Corollary | `c:p4:shadow` (line 2316) | Leading coefficients control zero shadows |
| Theorem | `c:p4:monadtaylor` (line 2327) | Exact monad-wide Taylor expansion |
| Theorem | `c:p4:derivbridge` (line 2356) | The section derivative is the fine derivative |
| Proposition | `c:p4:prop-units` (line 2406) | Units |
| Proposition | `c:p4:prop-calculus` (line 2428) | Infinitesimal functional calculus |
| Theorem | `c:p4:composition` (line 2455) | Admissible composition |
| Proposition | `c:p4:chartchange` (line 2499) | Chart-change criterion |
| Theorem | `c:p4:identity` (line 2545) | Identity theorem for coherent sections |
| Theorem | `c:p4:gluing` (line 2611) | Gluing over the ordinary base |
| Theorem | `c:p4:lift` (line 2659) | Functoriality of the lift |
| Proposition | `c:p4:liftzeros` (line 2687) | A lift creates no displaced zeros |
| Theorem | `c:p4:bridge` (line 2731) | Scale embedding of arbitrary formal series |
| Proposition | `c:p4:obstruction` (line 2766) | An obstruction in the original chart |
| Proposition | `c:p5:calculus` (line 2844) | Elementary calculus of the functional |
| Lemma | `c:p5:positivity` (line 2902) | Positivity of the coefficientwise integral |
| Theorem | `c:p5:ML` (line 2927) | Surcomplex ML inequality |
| Theorem | `c:p5:cauchy` (line 2992) | Cauchy's theorem and integral formula |
| Corollary | `c:p5:cauchyest` (line 3046) | Cauchy estimates from a pointwise surreal bound |
| Corollary | `c:p5:scaledCauchy` (line 3070) | Cauchy estimates in an affine chart |
| Lemma | `c:p5:csmajorant` (line 3102) | Cauchy--Schwarz majorant lemma |
| Proposition | `c:p5:majorant` (line 3118) | Coefficientwise Cauchy estimate |
| Theorem | `c:p5:morera` (line 3161) | Coefficientwise Morera |
| Theorem | `c:p5:primitive` (line 3198) | Coherent primitives |
| Lemma | `d:lem:ordinarydivision` (line 3353) | Ordinary division, extended coefficientwise |
| Theorem | `d:thm:preparation` (line 3394) | Hahn--Weierstrass preparation, global form |
| Corollary | `d:cor:localprep` (line 3519) | Local preparation at a single zero |
| Theorem | `d:thm:division` (line 3557) | Hahn--Weierstrass division |
| Lemma | `d:lem:smallroots` (line 3595) | All corrections are infinitesimal |
| Theorem | `d:thm:zerocluster` (line 3622) | Exact zero clustering; specialization of the zero divisor |
| Corollary | `d:cor:displacement` (line 3696) | Simple-root lifting and its displacement |
| Theorem | `d:thm:rouchevaluation` (line 3745) | Valuation Rouch\'e: fibrewise stability |
| Theorem | `d:thm:rouchemargin` (line 3762) | Ordinary-margin Rouch\'e: stability of the total |
| Corollary | `d:cor:rouchereal` (line 3794) | Real-margin Rouch\'e: a surcomplex-valued hypothesis |
| Theorem | `d:thm:moments` (line 3852) | Contour moments of a zero cluster |
| Theorem | `d:thm:Hresidue` (line 4035) | Cluster residue theorem on $\Mc(U)$ |
| Proposition | `d:prop:quotientinM` (line 4094) | Quotients of coherent families lie in $\Mc(U)$ |
| Theorem | `d:thm:bridge1` (line 4124) | Residue-cluster theorem |
| Theorem | `d:thm:residuequotient` (line 4195) | Residue theorem for coherent quotients, global form |
| Theorem | `d:thm:bridge2` (line 4234) | Uniformly bounded pole order |
| Theorem | `d:thm:weightedarg` (line 4311) | Exact weighted argument principle |
| Corollary | `d:cor:zerosminuspoles` (line 4371) | Zeros minus poles |
| Theorem | `d:thm:deformation` (line 4405) | Deformation invariance under admissible infinitesimal deformations |
| Theorem | `d:thm:rationalresidue` (line 4461) | Global rational residue theorem |
| Lemma | `e:lem-normalize` (line 4560) | Infinitesimal rescaling; monomial radius |
| Theorem | `e:thm-openmapping` (line 4615) | Local finite degree and the open mapping theorem |
| Corollary | `e:cor-maxmod` (line 4644) | Strong local maximum modulus |
| Lemma | `e:lem-reversion` (line 4683) | Hahn reversion |
| Theorem | `e:thm-localinverse` (line 4716) | Coherent local inverse |
| Proposition | `e:prop-autobounded` (line 4750) | Automatic surreal boundedness |
| Theorem | `e:thm-realliouville` (line 4782) | Real-bounded macroscopically entire functions |
| Theorem | `e:thm-coeffliouville` (line 4825) | Coefficientwise growth and polynomial degree |
| Theorem | `e:thm-removable` (line 4883) | Coefficientwise removal is necessary and sufficient |
| Theorem | `e:thm-schwarzpick` (line 4938) | Schwarz--Pick for canonical lifts |
| Corollary | `e:cor-schwarz` (line 4986) | Schwarz lemma for canonical lifts |
| Corollary | `e:cor-spstability` (line 5001) | Stability away from the equality case |
| Theorem | `e:thm-biholo` (line 5048) | Lifting of infinitesimally deformed biholomorphisms |
| Corollary | `e:cor-liftbiholo` (line 5085) | Lifted conformal equivalence |
| Corollary | `e:cor-riemannmap` (line 5091) | Standard-halo Riemann mapping theorem |
| Theorem | `e:thm-montel` (line 5126) | Countable-support Montel theorem |
| Theorem | `e:thm-harmonic` (line 5188) | Coefficientwise harmonic conjugates |
| Theorem | `e:thm-poisson` (line 5214) | Poisson's formula and a coherent Dirichlet problem |
| Theorem | `e:thm-reflection` (line 5253) | Coherent Schwarz reflection |
| Proposition | `e:prop-infexp` (line 5305) | Infinitesimal exponential and logarithm |
| Proposition | `e:prop-polar` (line 5338) | The finite exponential and the polar form |
| Theorem | `e:thm-exp` (line 5401) | Properties of the canonical exponential |
| Theorem | `e:thm-twisted` (line 5488) | The twisted global exponentials |
| Corollary | `e:cor-twistwitness` (line 5544) | A structured unit-modulus witness |
| Theorem | `e:thm-periodobstruction` (line 5566) | The period obstruction |
| Theorem | `e:thm-globallog` (line 5619) | A logarithm on the whole punctured class plane |
| Corollary | `e:cor-lognotcoherent` (line 5663) | $\mathcal L$ is not a coherent primitive of $1/z$ |
| Theorem | `e:thm-principallog` (line 5712) | Principal logarithm on the cut plane |
| Proposition | `e:prop-logdiscrepancy` (line 5738) | $\mathcal L$ and $\Log$ are different functions |
| Theorem | `e:thm-logcharts` (line 5782) | Logarithm charts on multiplicative monads |
| Theorem | `e:thm-picard` (line 5818) | Every nonzero value at every surreal scale |
| Theorem | `f:thm-affine` (line 5937) | Affine transport of the coherent theory |
| Proposition | `f:prop-chartchange` (line 6030) | Chart-change criterion |
| Corollary | `f:cor-scaledCauchy` (line 6084) | Cauchy estimates at an arbitrary coherent scale |
| Theorem | `f:thm-rigidity` (line 6156) | All-scale polynomial rigidity |
| Corollary | `f:cor-globalclassical` (line 6219) | Global classical consequences in the rigid category |
| Lemma | `f:lem-polefree` (line 6281) | A pole-free coherent fraction is coherent holomorphic |
| Theorem | `f:thm-rationalrigidity` (line 6335) | All-scale rational rigidity |

### analytic-geometry

Source: [surcomplex/analytic-geometry/article.tex](surcomplex/analytic-geometry/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `analytic:thm:overview-structure-A` (line 259) | Structure of the radius-free ring $\A_n$, overview |
| Theorem | `analytic:thm:overview-structure-R` (line 272) | Structure and finite maps for the common-domain ring $\RR_n$, overview |
| Theorem | `analytic:thm:overview-deform` (line 284) | Conservation, duality and the radius-free strengthening, overview |
| Theorem | `analytic:thm:overview-stability` (line 305) | Quantitative stability over $\A_n$, overview |
| Lemma | `analytic:lem:enlargement` (line 446) | Enlargement rule |
| Lemma | `analytic:lem:neumann` (line 479) | Hahn--Neumann support lemma |
| Lemma | `analytic:lem:operator` (line 508) | Positive-support operator inversion |
| Proposition | `analytic:prop:units` (line 603) | Units of $\A_n$ |
| Proposition | `analytic:prop:translation` (line 616) | Evaluation and translation over $\A_n$ |
| Proposition | `analytic:prop:kernels` (line 649) | Evaluation kernels and finite jets over $\A_n$ |
| Proposition | `analytic:prop:faithful` (line 670) | Faithful interpretation as functions on the monad |
| Proposition | `analytic:prop:evaluationR` (line 730) | Evaluation, support and translation over $\RR_n$ |
| Lemma | `analytic:lem:density` (line 767) | Infinitesimal evaluation detects nonzero elements of $\RR_n$ |
| Theorem | `analytic:thm:divisionA` (line 864) | Hahn-germ division over $\A_n$ |
| Theorem | `analytic:thm:prepA` (line 893) | Preparation and finite projection over $\A_n$ |
| Corollary | `analytic:cor:hypersurface-fiber` (line 930) | Fibres of a prepared hypersurface over $\A_n$ |
| Theorem | `analytic:thm:prepR` (line 978) | Parameterized Hahn preparation over $\RR_n$ |
| Theorem | `analytic:thm:divisionR` (line 1018) | Parameterized Hahn division over $\RR_n$ |
| Corollary | `analytic:cor:freehypersurfaceR` (line 1044) | Finite free hypersurface quotient over $\RR_n$ |
| Theorem | `analytic:thm:noetherianA` (line 1082) | Noetherianity of $\A_n$ |
| Theorem | `analytic:thm:weak-nullA` (line 1097) | Weak Nullstellensatz over $\A_n$ |
| Theorem | `analytic:thm:strong-nullA` (line 1127) | Jacobson property and strong Nullstellensatz over $\A_n$ |
| Theorem | `analytic:thm:regularA` (line 1159) | Local geometry of $\A_n$ |
| Theorem | `analytic:thm:noetherianR` (line 1209) | Noetherian monad ring $\RR_n$ |
| Proposition | `analytic:prop:normalization` (line 1238) | Noether normalization over $\RR_n$ |
| Theorem | `analytic:thm:weaknullR` (line 1262) | Weak monad Nullstellensatz over $\RR_n$ |
| Theorem | `analytic:thm:strongnullR` (line 1288) | Strong monad Nullstellensatz over $\RR_n$ |
| Proposition | `analytic:prop:completionR` (line 1331) | Local coordinates and completion over $\RR_n$ |
| Theorem | `analytic:thm:finitemap` (line 1377) | Finite projection and generic fibres over $\RR_n$ |
| Lemma | `analytic:lem:residue-annihilate` (line 1585) | Well-definedness and annihilation over $\A_n$ |
| Lemma | `analytic:lem:spanning` (line 1621) | Spanning with a support certificate, over $\A_n$ |
| Theorem | `analytic:thm:finite-deformA` (line 1642) | Finite complete-intersection deformation over $\A_n$: the radius-free strengthening |
| Theorem | `analytic:thm:conjugacy` (line 1734) | Positive Hahn conjugacy |
| Lemma | `analytic:lem:ordinarykoszul` (line 1777) | Ordinary contraction on one fixed neighbourhood |
| Theorem | `analytic:thm:conservationR` (line 1820) | Support-explicit conservation of multiplicity over $\RR_n$ |
| Corollary | `analytic:cor:matrices` (line 1900) | Infinitesimal coordinate eigenvalues |
| Theorem | `analytic:thm:residueduality` (line 1956) | Support-controlled residue duality over $\RR_n$ |
| Proposition | `analytic:prop:residues-agree` (line 2005) | The two residue functionals agree where both are defined |
| Corollary | `analytic:cor:residueframe` (line 2028) | A support-controlled constant residue frame |
| Lemma | `analytic:lem:finite-dependency` (line 2065) | Finite dependency at a prescribed exponent |
| Theorem | `analytic:thm:trace` (line 2086) | Trace--Jacobian identity |
| Theorem | `analytic:thm:zeros` (line 2138) | Conservation of singular zeros |
| Proposition | `analytic:prop:jacobian` (line 2185) | Four equivalent forms of the simple-root criterion |
| Corollary | `analytic:cor:weighted` (line 2200) | Weighted evaluation and simple residues |
| Theorem | `analytic:thm:workspace` (line 2253) | Workspace invariance over $\A_n$ |
| Theorem | `analytic:thm:basechange` (line 2283) | Base change and full surcomplex exhaustiveness over $\RR_n$ |
| Corollary | `analytic:cor:full-sc` (line 2315) | Full-surcomplex conservation |
| Theorem | `analytic:thm:formal-comparison` (line 2368) | Analytic--formal comparison |
| Lemma | `analytic:lem:scaled-polynomial` (line 2450) | Scaled Taylor polynomials at each Hahn exponent |
| Theorem | `analytic:thm:local-stability` (line 2468) | One-root Hensel--Rouch\'e bound over $\A_n$ |
| Corollary | `analytic:cor:separation` (line 2525) | Separation of simple zeros |
| Theorem | `analytic:thm:cluster-stability` (line 2542) | Finite-cluster correspondence |
| Corollary | `analytic:cor:nonpolynomial` (line 2980) | A nonpolynomial length-five cluster over $\RR_2$ |

### contours-and-stokes

Source: [surcomplex/contours-and-stokes/article.tex](surcomplex/contours-and-stokes/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `contours:lem:support` (line 386) | Support mechanism |
| Proposition | `contours:prop:fullfine` (line 551) | Full-class discreteness of sets |
| Proposition | `contours:prop:intrinsic` (line 582) | Intrinsic total separation |
| Proposition | `contours:prop:noftc` (line 632) | No endpoint integration for all fine-local primitives |
| Proposition | `contours:prop:mesh` (line 670) | Finite-partition obstruction |
| Theorem | `contours:thm:stdpartjordan` (line 728) | Jordan separation in the standard-part topology |
| Theorem | `contours:thm:sajordan` (line 802) | Semialgebraic Jordan theorem; classical input |
| Theorem | `contours:thm:polstokes` (line 945) | Polynomial-chain Stokes |
| Theorem | `contours:thm:hahnstokes` (line 1038) | Hahn-valued generalized Stokes |
| Proposition | `contours:prop:poincare` (line 1087) | Support-preserving Poincar\'e lemma |
| Theorem | `contours:thm:cohomology` (line 1109) | Cohomology of the globally supported Hahn complex |
| Lemma | `contours:lem:pullback` (line 1256) | Pullback and differential with a support certificate |
| Theorem | `contours:thm:deformedstokes` (line 1317) | Stokes for Hahn-deformed chains |
| Theorem | `contours:thm:homotopy` (line 1412) | Hahn homotopy formula |
| Proposition | `contours:prop:ml` (line 1459) | An order-valued parameter estimate |
| Theorem | `contours:thm:cauchy` (line 1520) | Coherent Cauchy theorem |
| Theorem | `contours:thm:endpoints` (line 1558) | Exact endpoint-transport formula |
| Theorem | `contours:thm:winding` (line 1635) | Winding stability at one scale |
| Theorem | `contours:thm:cauchyformula` (line 1668) | Cauchy formula at displaced points and on deformed contours |
| Corollary | `contours:cor:deformedres` (line 1738) | Residues on a deformed protecting contour |
| Proposition | `contours:prop:overlap` (line 1813) | Agreement on admissible overlaps |
| Theorem | `contours:thm:rescaling` (line 1904) | Positive rescaling gives polynomial coefficient families |
| Theorem | `contours:thm:localcauchy` (line 1971) | Cauchy formula for a radius-free germ |
| Lemma | `contours:lem:protect` (line 2004) | A radius protecting an entire one-variable cluster |
| Theorem | `contours:thm:microcircle` (line 2028) | Microscopic circle realization of the one-variable perturbation residue |
| Theorem | `contours:thm:localresidue` (line 2076) | Radius-free moving-pole residue theorem |
| Theorem | `contours:thm:microtorus` (line 2185) | Coordinate-power torus realization |
| Lemma | `contours:lem:residuetransform` (line 2273) | Transformation of the Hahn perturbation residue |
| Theorem | `contours:thm:generalrepresentation` (line 2311) | Microscopic contour representation of a general residue |
| Theorem | `contours:thm:septorus` (line 2444) | Separating-torus realization; conditional on \cite{Geometry} |
| Theorem | `contours:thm:algpairing` (line 2632) | Characterization and algebraic Cauchy theory |
| Proposition | `contours:prop:rationalcohomology` (line 2685) | Rational de Rham quotient |
| Proposition | `contours:prop:comparison` (line 2730) | Comparison on separated charts |
| Proposition | `contours:prop:samplingcriterion` (line 2847) | A precise sampling criterion |
| Theorem | `contours:thm:sampling` (line 2892) | Coefficientwise recovery of a Hahn contour |

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
| Corollary | `finite:cor:koszul` (line 748) | All Koszul relations lift, with an explicit preimage |
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
| Theorem | `finite:thm:monadcount` (line 1084) | Coherent conservation of isolated intersections |
| Theorem | `finite:thm:spectral` (line 1103) | Characteristic polynomials, traces and norms |
| Proposition | `finite:prop:separation` (line 1123) | A bounded list of separating linear forms |
| Proposition | `finite:prop:resdescend` (line 1176) | The residue descends to the finite algebra |
| Corollary | `finite:cor:coefficientresidue` (line 1187) | Explicit coefficient extraction for coordinate-power leading systems |
| Theorem | `finite:thm:duality` (line 1207) | Perfect integral residue duality |
| Corollary | `finite:cor:residuereconstruction` (line 1223) | Contour recovery of the finite algebra |
| Corollary | `finite:cor:relative` (line 1238) | Relative residue duality over a parameter domain |
| Lemma | `finite:lem:witness` (line 1268) | Finite-witness transfer |
| Lemma | `finite:lem:finitedependence` (line 1288) | The ordinary finite-parameter comparison |
| Theorem | `finite:thm:trace` (line 1300) | Trace--Jacobian identity and simple-zero residues |
| Theorem | `finite:thm:bezout` (line 1342) | Residue reproducing kernel |
| Theorem | `finite:thm:localres` (line 1386) | Moving-intersection residue theorem |
| Corollary | `finite:cor:transformation` (line 1406) | Change of generators |
| Theorem | `finite:thm:transform` (line 1415) | Coordinate change by an infinitesimal displacement |
| Theorem | `finite:thm:discriminant` (line 1435) | Discriminant--Jacobian identity and the reducedness criterion |
| Proposition | `finite:prop:univtrace` (line 1464) | One-variable trace and residue formulas, stable across collisions |
| Theorem | `finite:thm:monodromy` (line 1485) | Support-preserving lift of the ordinary root cover |
| Theorem | `finite:thm:precision` (line 1512) | Precision of normal forms, residues and spectral invariants |
| Corollary | `finite:cor:discstable` (line 1542) | A discriminant threshold that preserves simple zeros |
| Theorem | `finite:thm:rootstability` (line 1559) | Sharp conditioned root stability |
| Corollary | `finite:cor:matching` (line 1610) | Stable matching of an entire simple cluster |
| Proposition | `finite:prop:sharpness` (line 1619) | Both bounds attained, and the threshold strict |

### global-divisors

Source: [surcomplex/global-divisors/article.tex](surcomplex/global-divisors/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `global:lem:support` (line 227) | Support calculus |
| Proposition | `global:prop:evaluation` (line 275) | Evaluation and identity |
| Proposition | `global:prop:sheaf` (line 292) | Support-preserving sheaf property |
| Proposition | `global:prop:units` (line 304) | Exact unit criterion |
| Proposition | `global:prop:explog` (line 320) | Positive-support exponential and logarithm |
| Lemma | `global:lem:scalarML` (line 350) | Scalar Weierstrass and Mittag--Leffler |
| Lemma | `global:lem:hermite` (line 366) | Discrete Hermite interpolation |
| Lemma | `global:lem:scalarCousin` (line 387) | Scalar additive Cousin theorem on $\C$ |
| Theorem | `global:thm:preparation` (line 425) | Uniform-support local preparation |
| Corollary | `global:cor:roots` (line 458) | All roots in a monad |
| Lemma | `global:lem:division` (line 474) | Deformed division |
| Lemma | `global:lem:polefree` (line 498) | Pole-free fractions |
| Theorem | `global:thm:PID` (line 512) | Principal-ideal-domain stalks |
| Proposition | `global:prop:nonlocal` (line 534) | Non-locality, and the integral model |
| Corollary | `global:cor:Picmeaning` (line 548) | Meaning of the Picard group here |
| Theorem | `global:thm:ML` (line 592) | Uniform-support Mittag--Leffler criterion |
| Corollary | `global:cor:interp` (line 618) | Entire interpolation with an exact support criterion |
| Theorem | `global:thm:divisor` (line 638) | Sharp global moving-divisor criterion |
| Proposition | `global:prop:realizationtorsor` (line 692) | The freedom in realization |
| Corollary | `global:cor:splitting` (line 762) | Failure of arbitrary global divisor splitting |
| Proposition | `global:prop:restrictedalgebra` (line 796) | Restricted product algebra |
| Theorem | `global:thm:interpolation` (line 812) | Deformed Hermite interpolation |
| Corollary | `global:cor:CRT` (line 835) | Chinese remainder quotient |
| Theorem | `global:thm:MLmoving` (line 876) | Sharp moving-pole Mittag--Leffler theorem |
| Theorem | `global:thm:aut` (line 913) | Global inverse for positive-support perturbations |
| Corollary | `global:cor:motion` (line 937) | Exact interpolation of simple motions |
| Theorem | `global:thm:cousincriterion` (line 975) | Necessary and sufficient Cousin criterion |
| Theorem | `global:thm:obstruction` (line 1013) | A concrete obstruction subspace |
| Corollary | `global:cor:H1injection` (line 1040) | First cohomology detected by descending scales |
| Corollary | `global:cor:H1size` (line 1058) | Size and local invisibility |
| Proposition | `global:prop:divPic` (line 1085) | The divisor and logarithmic obstructions coincide |
| Proposition | `global:prop:Picreduction` (line 1099) | Reduction of the Picard group to positive supports |
| Lemma | `global:lem:descending` (line 1122) | Descending positive sequences |
| Theorem | `global:thm:dichotomy` (line 1130) | Picard-group vanishing dichotomy |
| Theorem | `global:thm:dimension` (line 1159) | Continuum many independent classes, and the exact dimension |
| Proposition | `global:prop:fullH1` (line 1184) | The full additive sheaf is already obstructed in cyclic rank |
| Proposition | `global:prop:Cartierexample` (line 1208) | An effective divisor with trivial ordinary reduction but no global equation |

### polynomial-algebra

Source: [surcomplex/polynomial-algebra/article.tex](surcomplex/polynomial-algebra/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Proposition | `polynomial:prop:workspace` (line 376) | A workspace for every set of data |
| Lemma | `polynomial:lem:support` (line 475) | Hahn--Neumann support calculus |
| Theorem | `polynomial:thm:fta` (line 586) | Finite polynomial algebra over $K$ |
| Theorem | `polynomial:thm:crt` (line 647) | Finite Hermite interpolation and CRT |
| Proposition | `polynomial:prop:rootbounds` (line 725) | Cauchy bounds and a radial bound |
| Theorem | `polynomial:thm:gausslucas` (line 762) | Surcomplex Gauss--Lucas |
| Proposition | `polynomial:prop:weighted` (line 791) | Weighted incomplete polynomials, and a converse |
| Theorem | `polynomial:thm:jensen` (line 817) | Surcomplex Jensen disk theorem |
| Lemma | `polynomial:lem:compression` (line 861) | Differentiating compression |
| Lemma | `polynomial:lem:schur` (line 872) | Finite-dimensional Schur inequality |
| Theorem | `polynomial:thm:schoenberg` (line 891) | Sharp surcomplex Schoenberg inequality |
| Theorem | `polynomial:thm:orderrouche` (line 966) | Rouch\'e on an order-modulus circle |
| Corollary | `polynomial:cor:pellet` (line 996) | Monomial dominance |
| Theorem | `polynomial:thm:hermite` (line 1047) | Hermite's signature criterion over surreal real closed fields |
| Theorem | `polynomial:thm:pseudozeros` (line 1105) | Exact uncertainty root sets in two geometries |
| Lemma | `polynomial:lem:gaussvaluation` (line 1193) | Multiplicativity |
| Theorem | `polynomial:thm:initialroots` (line 1216) | Initial polynomial and all residue-direction root counts |
| Corollary | `polynomial:cor:valrouche` (line 1272) | Valuation Rouch\'e: preservation of the whole initial polynomial |
| Theorem | `polynomial:thm:newton` (line 1317) | Newton's root-valuation rule |
| Theorem | `polynomial:thm:imageballs` (line 1419) | Exact image and fiber degree |
| Corollary | `polynomial:cor:normalization` (line 1461) | Affine normalization of a finite polynomial problem |
| Theorem | `polynomial:thm:finitemap` (line 1491) | A polynomial is a finite flat map of its degree |
| Theorem | `polynomial:thm:branchvalues` (line 1515) | Branch-value polynomial |
| Proposition | `polynomial:prop:ramification` (line 1543) | Finite and infinite ramification |
| Corollary | `polynomial:cor:polynomialmaps` (line 1564) | Surjectivity and polynomial injections |
| Lemma | `polynomial:lem:initialderivative` (line 1584) | The derivative of an initial polynomial |
| Theorem | `polynomial:thm:criticalballs` (line 1607) | Exact critical-point conservation in occupied balls |
| Corollary | `polynomial:cor:ramificationball` (line 1639) | Ramification count on an arbitrary mapping ball |
| Corollary | `polynomial:cor:nearest` (line 1660) | Valuative Gauss--Lucas and nearest neighbours |
| Theorem | `polynomial:thm:branch` (line 1686) | Critical residue directions inside a cluster |
| Corollary | `polynomial:cor:tree` (line 1748) | Critical allocation by the root tree |
| Proposition | `polynomial:prop:clusterdisc` (line 1815) | Discriminant as a finite level sum |
| Proposition | `polynomial:prop:disctree` (line 1837) | Discriminant as a sum over the root tree |
| Theorem | `polynomial:thm:hensel` (line 1889) | Support-controlled coprime Hensel factorization |
| Corollary | `polynomial:cor:simpleroot` (line 1942) | Simple-root lifting and the first correction |
| Corollary | `polynomial:cor:clusterfactor` (line 1961) | Canonical standard-part cluster factors |
| Theorem | `polynomial:thm:parameterhensel` (line 1999) | Parameter factor lifting without repeated shrinking |
| Theorem | `polynomial:thm:holder` (line 2081) | Optimal valuation-H\"older root matching |
| Corollary | `polynomial:cor:derivativeholder` (line 2132) | Simultaneous stability for derivatives |
| Theorem | `polynomial:thm:stability` (line 2182) | Exact matching, full cluster stability, and a second-order Newton error |
| Corollary | `polynomial:cor:discprecision` (line 2309) | Discriminant precision protects all clusters |
| Corollary | `polynomial:cor:treestability` (line 2388) | Preservation of the tree and of its critical directions |
| Theorem | `polynomial:thm:residuepairing` (line 2464) | Universal residue pairing and explicit dual basis |
| Theorem | `polynomial:thm:trace` (line 2524) | Universal trace identity |
| Proposition | `polynomial:prop:localresidues` (line 2595) | Finite residue formula at multiple roots |
| Proposition | `polynomial:prop:tracenormroots` (line 2636) | Field-level traces and norms, including collisions |
| Theorem | `polynomial:thm:discriminant` (line 2661) | Discriminant and trace-pairing degeneration |
| Lemma | `polynomial:lem:zariski` (line 2747) | Zariski's lemma in the needed form |
| Theorem | `polynomial:thm:nullstellensatz` (line 2775) | Surcomplex Nullstellensatz |
| Proposition | `polynomial:prop:finitealgebra` (line 2837) | Finite fibers and local lengths |
| Theorem | `polynomial:thm:globalfree` (line 2926) | Global finite-free normal forms |
| Corollary | `polynomial:cor:globalbezout` (line 2978) | A global B\'ezout count, including infinite-scale roots |
| Theorem | `polynomial:thm:multiperfect` (line 3037) | A coefficient-independent perfect pairing |
| Theorem | `polynomial:thm:jacobian` (line 3078) | B\'ezoutian kernel and Jacobian duality |
| Corollary | `polynomial:cor:eulerjacobi` (line 3133) | Simple-root weights and Euler--Jacobi vanishing |
| Theorem | `polynomial:thm:polyparameters` (line 3177) | Global polynomial families on one ordinary parameter domain |
| Theorem | `polynomial:thm:analyticcomparison` (line 3219) | Polynomial identification of the Jacobian trace element |

### trigonometry

Source: [surcomplex/trigonometry/article.tex](surcomplex/trigonometry/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `trigonometry:lem:support` (line 349) | Hahn--Neumann support calculus |
| Proposition | `trigonometry:prop:topology` (line 399) | Degeneracy of fine convergence |
| Proposition | `trigonometry:prop:lift` (line 431) | Local calculus and one-variable sign lifting |
| Lemma | `trigonometry:lem:leading` (line 460) | Leading-term test for a lifted germ |
| Theorem | `trigonometry:thm:identities` (line 500) | Elementary trigonometry on finite surreal angles |
| Proposition | `trigonometry:prop:order` (line 540) | Signs and monotonicity |
| Proposition | `trigonometry:prop:leading` (line 565) | Exact infinitesimal leading orders |
| Proposition | `trigonometry:prop:normalization` (line 588) | Normalization of the finite trigonometric pair |
| Proposition | `trigonometry:prop:rotation` (line 638) | Algebraic angle addition and rotations |
| Theorem | `trigonometry:thm:polar` (line 664) | Polar decomposition and the angle group |
| Corollary | `trigonometry:cor:representatives` (line 697) | Representatives, roots, and torsion |
| Theorem | `trigonometry:thm:cayley` (line 743) | Projective half-angle parametrization of every surreal direction |
| Theorem | `trigonometry:thm:inverse` (line 782) | Inverse tangent, sine, and cosine |
| Proposition | `trigonometry:prop:acosendpoint` (line 852) | Endpoint ramification of inverse cosine |
| Theorem | `trigonometry:thm:metric` (line 880) | Angular and chordal comparison |
| Corollary | `trigonometry:cor:phaseisometry` (line 912) | Local valuation isometry of phase and rotation displacement |
| Corollary | `trigonometry:cor:directionstability` (line 936) | Stability of direction under a relative perturbation |
| Theorem | `trigonometry:thm:anglesum` (line 969) | Euclidean angle sum over the surreal field |
| Theorem | `trigonometry:thm:trianglelaws` (line 991) | Triangle laws |
| Corollary | `trigonometry:cor:right` (line 1019) | Right triangles and the full range of slopes |
| Theorem | `trigonometry:thm:sss` (line 1030) | Existence, congruence, and similarity |
| Theorem | `trigonometry:thm:heron` (line 1079) | Heron, half-angle, incircle and bisector formulas |
| Theorem | `trigonometry:thm:euler` (line 1118) | Euler's incentre--circumcentre identity |
| Corollary | `trigonometry:cor:areabound` (line 1140) | A scale-independent area inequality |
| Theorem | `trigonometry:thm:cevian` (line 1155) | Sine ratios for a cevian |
| Theorem | `trigonometry:thm:ceva` (line 1172) | Trigonometric Ceva |
| Proposition | `trigonometry:prop:inscribed` (line 1211) | Inscribed-angle theorem |
| Theorem | `trigonometry:thm:ptolemy` (line 1224) | Ptolemy inequality and its cyclic equality case |
| Corollary | `trigonometry:cor:polygon` (line 1253) | Finite regular polygons at surreal scale |
| Theorem | `trigonometry:thm:valuationtriangle` (line 1299) | Valuation form of the triangle laws |
| Theorem | `trigonometry:thm:defect` (line 1338) | A quadratic defect formula |
| Theorem | `trigonometry:thm:flat` (line 1370) | Quadratic slack and reciprocal circumradius in normalized coordinates |
| Theorem | `trigonometry:thm:flatrelative` (line 1408) | Exact gap identity and the relative flatness threshold |
| Theorem | `trigonometry:thm:amplitude` (line 1545) | Amplitude--phase reduction and intersection count |
| Theorem | `trigonometry:thm:tangency` (line 1581) | Tangency, angular splitting, and loss of valuation |
| Theorem | `trigonometry:thm:fold` (line 1623) | The cosine fold |
| Theorem | `trigonometry:thm:residuepairing` (line 1665) | A collision-stable residue pairing |
| Lemma | `trigonometry:lem:hensel` (line 1763) | A simple residue root of a polynomial |
| Theorem | `trigonometry:thm:stability` (line 1782) | Sharp angular root-stability bound |
| Proposition | `trigonometry:prop:sharp` (line 1837) | The threshold and both exponents are sharp |
| Theorem | `trigonometry:thm:conditioned` (line 1861) | Conditioned inversion of cosine |
| Theorem | `trigonometry:thm:stripexp` (line 1946) | Canonical strip exponential |
| Theorem | `trigonometry:thm:striptrig` (line 1977) | Complex-variable identities and zero sets |
| Theorem | `trigonometry:thm:sinefibers` (line 2004) | Surjectivity and complete fibres of strip sine |
| Corollary | `trigonometry:cor:sineinverse` (line 2029) | Explicit inverse branches |
| Theorem | `trigonometry:thm:polyroots` (line 2066) | Algebraization and the $2n$ root bound |
| Corollary | `trigonometry:cor:chebyshev` (line 2098) | Chebyshev and extremum equations |
| Theorem | `trigonometry:thm:cluster` (line 2128) | Exact cluster multiplicity and coefficient support |
| Theorem | `trigonometry:thm:fourier` (line 2205) | Finite Fourier inversion, sampling, and Parseval |
| Theorem | `trigonometry:thm:parseval` (line 2263) | Finite Fourier identities over $\SC$ |
| Lemma | `trigonometry:lem:twosquares` (line 2319) | Nonnegative polynomials over a real closed field |
| Theorem | `trigonometry:thm:fejer` (line 2333) | Surcomplex Fej\'er--Riesz theorem |
| Corollary | `trigonometry:cor:coeffbounds` (line 2395) | Fourier coefficient bounds from positivity |
| Theorem | `trigonometry:thm:spherical` (line 2463) | Spherical cosine and sine laws |
| Proposition | `trigonometry:prop:diskmetric` (line 2515) | Disk invariance and metric properties |
| Theorem | `trigonometry:thm:hyperbolic` (line 2545) | Hyperbolic triangle laws over $\No$ |
| Theorem | `trigonometry:thm:arcs` (line 2607) | Circle length and sector area at every radius |
| Proposition | `trigonometry:prop:perimeters` (line 2634) | Failure of fine convergence of inscribed perimeters |
| Theorem | `trigonometry:thm:globalexp` (line 2711) | Canonical global exponential and its period class |
| Corollary | `trigonometry:cor:globalzeros` (line 2750) | Zero classes and periods |
| Theorem | `trigonometry:thm:characters` (line 2771) | All extensions of the finite phase |
| Theorem | `trigonometry:thm:infiniteperiods` (line 2819) | Infinite periods are unavoidable |
| Theorem | `trigonometry:thm:infinitefrequency` (line 2854) | No coherent infinite-frequency bounded sine |
| Theorem | `trigonometry:thm:allscale` (line 2879) | Why all-scale coherence forces a polynomial |

### broadcast-sum-of-surreal-sequences

Source: [surreal/broadcast-sum-of-surreal-sequences/article.tex](surreal/broadcast-sum-of-surreal-sequences/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:rank-monotone` (line 341) | Monotonicity of the auxiliary rank |
| Theorem | `thm:rank` (line 359) | Well-foundedness and a birthday bound |
| Lemma | `lem:commute` (line 407) | Commutation |
| Lemma | `lem:legalize` (line 425) | A nonidentity action can be legalized |
| Lemma | `lem:survive` (line 441) | The earlier witness survives |
| Theorem | `thm:number` (line 455) | Every broadcast game is a number |
| Proposition | `prop:basic` (line 502) | Relabelling, zeros, and negation |
| Theorem | `thm:finite-support` (line 519) | Finite-support agreement |
| Corollary | `cor:ordinal` (line 541) | Ordinal extension |
| Theorem | `thm:perturbation` (line 566) | Finite-short-perturbation bound |
| Corollary | `cor:cofinite` (line 624) | Untitled |
| Lemma | `lem:X-cuts` (line 645) | Untitled |
| Theorem | `thm:constants` (line 672) | Constant dyadic values and finite defects |
| Corollary | `cor:dyadic-tail` (line 729) | Cofinite dyadic leading scale |
| Lemma | `lem:left-family` (line 759) | Left options |
| Lemma | `lem:right-family` (line 786) | Right options |
| Theorem | `thm:finite-E` (line 808) | Untitled |
| Theorem | `thm:infinite-E` (line 827) | Untitled |
| Lemma | `lem:pure-power` (line 872) | Pure geometric tails |
| Corollary | `cor:nonmonotone` (line 886) | Failure of weak monotonicity |
| Corollary | `cor:scaling` (line 906) | Failure of finite-scaling compatibility |

### canonical-forms-need-not-be-subgraphs

Source: [surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex](surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:pentagon` (line 452) | A pentagon represents $1/2$ |
| Theorem | `thm:second-pentagon` (line 527) | A second pentagon of value $1/2$ |
| Lemma | Line 641 (unlabeled) | Convexity of a simplicity cone |
| Lemma | Line 659 (unlabeled) | Descent toward a prefix |
| Theorem | `thm:prefix-occurrence` (line 682) | Prefix occurrence |
| Lemma | Line 716 (unlabeled) | The finite canonical prefix chain |
| Theorem | `thm:prefix-path` (line 769) | A path through every finite prefix |
| Lemma | Line 802 (unlabeled) | One-sided finite cuts have integer values |
| Theorem | `thm:minima` (line 816) | Exact graph minima |
| Corollary | Line 861 (unlabeled) | Untitled |
| Lemma | Line 877 (unlabeled) | Forest obstruction |
| Theorem | `thm:minimal-forms` (line 904) | The vertex-minimal forms |
| Corollary | Line 960 (unlabeled) | Unique edge-minimizer |
| Lemma | Line 1005 (unlabeled) | Triangle-free forms on at most four vertices |
| Theorem | `thm:smallest` (line 1041) | Smallest size and rank of a counterexample |
| Proposition | Line 1085 (unlabeled) | A rank-minimal non-containing form |
| Lemma | Line 1179 (unlabeled) | Untitled |
| Theorem | `thm:odd-cycle` (line 1196) | Odd-cycle family |
| Lemma | Line 1245 (unlabeled) | Untitled |
| Theorem | `thm:odd-cycle-two` (line 1259) | Second odd-cycle family |
| Theorem | `thm:even-cycle` (line 1302) | Even-cycle family |
| Proposition | Line 1333 (unlabeled) | All cycle lengths except four |
| Theorem | `thm:extremal` (line 1352) | Exact extremal function for $1/2$ |
| Theorem | `thm:high-girth` (line 1425) | Spaced-spine construction |
| Corollary | Line 1495 (unlabeled) | Unbounded girth at every fixed value |
| Corollary | Line 1509 (unlabeled) | Avoiding every fixed cyclic graph |
| Proposition | Line 1525 (unlabeled) | A Fibonacci bound on the unfolded leaves |
| Proposition | Line 1562 (unlabeled) | A denominator-sensitive bound, second proof |
| Lemma | Line 1662 (unlabeled) | Separated integer markers |
| Lemma | Line 1710 (unlabeled) | Value preservation |
| Lemma | Line 1723 (unlabeled) | No unintended identifications |
| Lemma | Line 1752 (unlabeled) | Graph bounds |
| Theorem | `thm:sparse` (line 1781) | Planar high-girth representation theorem |
| Lemma | Line 1835 (unlabeled) | A triangle in every noninteger canonical graph |
| Theorem | `thm:integer-classification` (line 1854) | Exactly the integers, unlabelled version |
| Theorem | `thm:classification-rooted` (line 1889) | Exactly the integers, rooted-colour version |
| Proposition | Line 1956 (unlabeled) | A limit-stage coherence obstruction |
| Proposition | Line 2026 (unlabeled) | Exact high-girth forms of $\omega$ |
| Proposition | Line 2065 (unlabeled) | No transfinite form has finite outdegree everywhere |

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
| Proposition | Line 590 (unlabeled) | Cofinality is the invariant |
| Theorem | `thm:auto` (line 615) | Untitled |
| Theorem | `thm:independent` (line 659) | Ordinal-indexed finite linear independence |
| Proposition | `prop:rational` (line 769) | Rational primitives remain unique |
| Proposition | `prop:field` (line 797) | Untitled |

### gonshor-laurent-birthdays

Source: [surreal/gonshor-laurent-birthdays/article.tex](surreal/gonshor-laurent-birthdays/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Theorem | `thm:main` (line 143) | Laurent-series restriction |
| Lemma | `lem:add` (line 253) | Untitled |
| Lemma | `lem:realproduct` (line 291) | Real scalar product bound |
| Lemma | `lem:prefix` (line 332) | Prefixes and countable unions |
| Lemma | `lem:block` (line 355) | Untitled |
| Theorem | `thm:ordinalpoly` (line 388) | Ordinal-exponent polynomials |
| Theorem | `thm:finiteformula` (line 460) | Finite Laurent formula |
| Corollary | `cor:split` (line 538) | Exact finite splitting |
| Lemma | `lem:bounded` (line 579) | Untitled |
| Lemma | `lem:degree` (line 615) | Untitled |
| Lemma | `lem:crossmono` (line 637) | Positive monomial times bounded part |
| Corollary | `cor:crosspoly` (line 687) | Untitled |
| Theorem | `thm:finiteproduct` (line 704) | Finite Laurent product theorem |
| Corollary | `cor:strict` (line 733) | Equality with a finite negative tail |
| Theorem | `thm:infinite` (line 776) | Infinite Laurent birthday formula |
| Lemma | `lem:jets` (line 820) | Finite-jet stabilization |
| Corollary | `cor:reciprocal` (line 923) | Untitled |
| Corollary | `cor:spectrum` (line 957) | Untitled |

### gonshor-product-birthdays

Source: [surreal/gonshor-product-birthdays/surreal_product_birthdays.tex](surreal/gonshor-product-birthdays/surreal_product_birthdays.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | Line 254 (unlabeled) | Untitled |
| Lemma | Line 285 (unlabeled) | Untitled |
| Proposition | Line 330 (unlabeled) | Untitled |
| Theorem | Line 451 (unlabeled) | Exact birthday |
| Corollary | Line 573 (unlabeled) | Untitled |
| Theorem | Line 595 (unlabeled) | Sharp support bound |
| Proposition | Line 625 (unlabeled) | Strict degree gap |
| Lemma | Line 664 (unlabeled) | Dyadic factors |
| Lemma | Line 689 (unlabeled) | A dyadic scalar cannot increase the leading birthday data |
| Theorem | Line 740 (unlabeled) | Product birthdays on \(\A\) |
| Corollary | Line 764 (unlabeled) | Degree does not rise |
| Proposition | Line 799 (unlabeled) | No full convolution is needed |
| Proposition | Line 946 (unlabeled) | Untitled |
| Proposition | Line 975 (unlabeled) | Untitled |

### hahn-evaluation-at-omega

Source: [surreal/hahn-evaluation-at-omega/article.tex](surreal/hahn-evaluation-at-omega/article.tex).

| Kind | Source label or line | Heading |
|---|---|---|
| Lemma | `lem:witness` (line 311) | The formal square-root witness |
| Theorem | `thm:main` (line 347) | Negative answer to Problem 7.7 |
| Proposition | `prop:small` (line 380) | Untitled |
| Lemma | `lem:H` (line 499) | The nonnegative witness pair |
| Theorem | `thm:semiring` (line 535) | Nonnegative-coefficient obstruction |
| Lemma | `lem:unitsquare` (line 591) | Square roots of formal units |
| Lemma | `lem:unit-root` (line 612) | Square roots of units, general form |
| Theorem | `thm:necessary` (line 637) | Necessary infinitesimal condition |
| Proposition | `prop:kernel` (line 657) | The kernel dichotomy |
| Theorem | `thm:exact` (line 695) | Exactly which values of $x$ occur |
| Lemma | `lem:positivesquare` (line 839) | Every canonically positive element is a square |
| Theorem | `thm:orderforced` (line 859) | Order is algebraically forced |
| Theorem | `thm:reversal` (line 904) | Exponent-reversing isomorphism |
| Theorem | `thm:classification` (line 972) | Complete existence criterion for pure monomial data |
| Proposition | `prop:rational` (line 1093) | Untitled |
| Proposition | `prop:algebraic` (line 1167) | Criterion for a simple algebraic extension |
| Lemma | `lem:subseq` (line 1412) | Nondecreasing subsequences |
| Lemma | `lem:higman` (line 1440) | Higman's lemma, well-ordered alphabet case |
| Lemma | `lem:neumann` (line 1479) | Positive-support summability |
| Corollary | `cor:convolution` (line 1524) | Untitled |
| Lemma | `lem:two-supports` (line 1553) | Two supports, elementarily |
| Corollary | `cor:substitution` (line 1575) | Substitution into a positive-support series |
| Proposition | `prop:field` (line 1605) | Untitled |
