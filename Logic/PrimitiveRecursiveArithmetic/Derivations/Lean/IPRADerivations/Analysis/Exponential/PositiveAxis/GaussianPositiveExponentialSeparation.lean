import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialTermBound
import IPRADerivations.Analysis.FiniteOperations.GaussianPositiveScalarProductBound
import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialLinearRemainder

/-!
# A genuine lower slope of the original positive finite exponential

The first two original terms and the nonnegative remaining terms show
that an actual positive argument is no larger than its finite
exponential minus one. This reflects an observed exponential distance
to one back to the argument, with no loss in its rational radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveExponentialSeparation

open_ipra
open GaussianPositiveRealArithmetic (positive)
open GaussianRationalHorner (qadd canonical)
open GaussianRationalSyntheticDivision (qone qadd_congr qsub_congr)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody inverseFactorial scalar_sum_zero scalar_sum_succ)
open GaussianRationalExponentialTail (scalarPrefix tail prefix_split)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem linear_prefix (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    scalarPrefix q two ≐ qadd qone q := by
  have f : Γ ⊢[PRAAx] Products.fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _))
  have inv : Γ ⊢[PRAAx] inverseFactorial (one : PTm n) ≐ qone :=
    GaussianIntegerFractionPowers.fraction_congr (.eqRefl _) f
  exact (scalar_sum_succ q zero).eqTrans (qadd_congr (scalar_sum_zero q)
    ((GaussianRationalSyntheticDivision.qmul_congr inv (GaussianRationalPowerAlgebra.power_one q hq)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical q hq)))

theorem difference_decomposition (q K : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    qsub (scalarSum q K) qone ≐ qadd q (tail q two (monus K one)) := by
  let k := monus K one
  have e : Γ ⊢[PRAAx] succ K ≐ two+k := (congrSucc (eq_add_of_le hK)).eqTrans (by ipra_ring)
  have full : Γ ⊢[PRAAx] scalarSum q K ≐ qadd qone (qadd q (tail q two k)) :=
    (GaussianRationalFiniteSum.sum_index_congr scalarBody e (.eqRefl _)).eqTrans
      ((prefix_split q two k).eqTrans ((qadd_congr (linear_prefix q hq) (.eqRefl _)).eqTrans
        (GaussianRationalSumAlgebra.qadd_associative _ _ _)))
  exact (qsub_congr full (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (GaussianRationalHorner.qadd_canonical _ _))

theorem argument_order (q K : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (hp : Γ ⊢[PRAAx] positive q) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT q) (fstT (qsub (scalarSum q K) qone)) := by
  have suffix := GaussianPositiveExponentialTermBound.positive_suffix q two (monus K one) hp
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    ((RationalGaussianRealPart.real_add _ _).eqSymm.eqTrans (congrFst (difference_decomposition q K hq hK)).eqSymm)
    (GaussianPositiveExponentialProduct.scalar_le_add _ _ hq.andE₂.andE₁ suffix.andE₂)

/-- Exact reflection at the SAME actual finite sum, for every internal K>=1. -/
theorem finite_distance_reflection (q K A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] canonical q) (hp : Γ ⊢[PRAAx] positive q) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] distanceBounded (scalarSum q K) qone A D) : Γ ⊢[PRAAx] bounded q A D := by
  let v := qsub (scalarSum q K) qone
  have vc : Γ ⊢[PRAAx] canonical v := GaussianRationalMetric.qsub_canonical _ _
  have va : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis v := RationalGaussianEmbedding.axis_add _ _
    (GaussianPositiveExponentialProduct.positive_scalar_sum q K hp).andE₁
    (RationalGaussianEmbedding.axis_negative _ RationalGaussianEmbedding.axis_one)
  have small := GaussianPositiveScalarProductBound.product_bound_monotone qone q v A D hD hq vc hp va
    (argument_order q K hq hp hK)
    (bound_congr (GaussianPolynomialDeterminantTerms.one_mul_canonical v vc).eqSymm (.eqRefl _) (.eqRefl _) h)
  exact bound_congr (GaussianPolynomialDeterminantTerms.one_mul_canonical q hq) (.eqRefl _) (.eqRefl _) small

theorem original_cutoff_positive (R p : PTm n) : Γ ⊢[PRAAx] le one (GaussianRadiusExponentialName.index R p) := by
  have b : Γ ⊢[PRAAx] le two (GaussianRationalExponentialTail.cutoff R (p+num 4)) := by
    unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le 𝔞(p)+2*𝔞(R)+2*𝔞(R)^2+6
  exact (succ_monus_succ one _).eqSymm.eqTrans
    (le_congr (.eqRefl _) (GaussianRationalExponentialTail.last_successor R (p+num 4)).eqSymm b)

theorem original_constant_distance_reflection (q R p A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] canonical q) (hp : Γ ⊢[PRAAx] positive q)
    (h : Γ ⊢[PRAAx] distanceBounded (GaussianRadiusExponentialName.sample GaussianGammaCanonicalExponent.constantF R p q) qone A D) : Γ ⊢[PRAAx]
    bounded q A D := by
  have read := (GaussianRadiusExponentialName.sample_at (Γ := Γ) GaussianGammaCanonicalExponent.constantF R p q).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at _ _))
  exact finite_distance_reflection q _ A D hD hq hp (original_cutoff_positive R p)
    (GaussianRationalDistanceOrder.distance_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _) h)

theorem original_positive_exponential_distance_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 4) ⋏ (canonical (var 0) ⋏ positive (var 0))) ⟶
      distanceBounded (GaussianRadiusExponentialName.sample GaussianGammaCanonicalExponent.constantF (var 1) (var 2) (var 0)) qone (var 3) (var 4) ⟶
        bounded (var 0) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (original_constant_distance_reflection _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPositiveExponentialSeparation
