import IPRADerivations.Analysis.GaussianGammaNegativeProductDerivative
import IPRADerivations.Analysis.GaussianGammaNegativeCriticalCorrection
import IPRADerivations.Analysis.GaussianGammaDigammaSeriesTerms
import IPRADerivations.Analysis.GaussianScalarColumnSelection
import IPRADerivations.Analysis.GaussianRationalExponentialTangent

/-!
# The literal reciprocal correction of the Gamma shift product

The negative factors of the native shift product are the reversed
pole factors. Each has inverse equal to the negative of the original
positive reciprocal row. The final factor contributes the remaining
positive reciprocal. The derivative therefore multiplies the exact
original rising product by the negative of the literal correction.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeCorrection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode)
open GaussianGammaLocalPoleGuards (center)
open GaussianGammaNegativeCriticalCorrection (bottomDen correction guard positiveSum row row_den_positive)
open GaussianGammaNegativeProductDerivative (difference_product_zero dividedDifference firstCoefficient prefixDifference rising_product)
open GaussianGammaPoleFiniteFactors (difference differenceBody differenceProduct difference_succ)
open GaussianGammaRepeatedShift (risingProduct)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalDistanceOrder (reversed_difference)
open GaussianRationalHorner
  (canonical canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents qadd qmul qzero represents_congr)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qzero_add qzero_canonical qone qmul_zero_right)
open GaussianReciprocalHorner (qadd_commutative qmul_associative qmul_one_right)
open GaussianStirlingGammaLogarithm (arg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem denominator_positive (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] le one b := le_trans h.andE₁ (le_of_lt h.andE₂)

private theorem zero_minus (x : PTm n) : Γ ⊢[PRAAx] qsub qzero x ≐ qnegative x :=
  qzero_add _ (qnegative_canonical _)

private theorem product_prefix_canonical (h b j : PTm n) : Γ ⊢[PRAAx] canonical (differenceProduct h b j) :=
  GaussianRationalFiniteProduct.product_canonical differenceBody j (pairT h b)

theorem negative_factor (a b j : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] difference (arg a) b (succ j) ≐ qnegative (fraction (bottomDen a b j) b) := by
  let d := bottomDen a b j
  let v := scale d oneCode
  have hb := denominator_positive a b h
  have oa : Γ ⊢[PRAAx] le a (succ j*b) := le_trans (le_of_lt h.andE₂) (by ipra_le 𝔞 j*𝔞 b)
  have e := natEq (eq_add_of_le oa)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (center (arg a) b (succ j)) (ComplexLogarithmRemainder.neg v) := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [center,arg,GaussianGammaPoleZeros.poleNumerator,v,d,bottomDen,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_one]
      ipra_simps
      linear_combination -e
    · simp only [center,arg,GaussianGammaPoleZeros.poleNumerator,v,
        GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_neg,GaussianRootAlgebra.im_one]
      ring
  have rep := qnegative_represents (fraction d b) v b (ofGaussian_represents v b hb)
  exact canonical_unique _ _ _ b (ofGaussian_canonical _ _ hb) (qnegative_canonical _) hb
    (represents_congr (.eqRefl _) same (.eqRefl _) (ofGaussian_represents _ _ hb)) rep

private theorem reciprocal_fractions (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (fraction a b) (fraction b a) ≐ qone :=
  (GaussianStirlingOddCoefficients.fraction_product a b b a hb ha).eqTrans
    ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (mul_comm b a)).eqTrans
      (GaussianRationalExponentialTangent.fraction_one (a*b) (GaussianRationalHorner.positive_product _ _ ha hb)))

theorem negative_factor_inverse (a b j : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] qmul (difference (arg a) b (succ j)) (qsub qzero (row a b j)) ≐ qone :=
  (qmul_congr (negative_factor a b j h) (zero_minus (row a b j))).eqTrans
    ((GaussianScalarColumnSelection.negative_both_product _ _).eqTrans
      (reciprocal_fractions (bottomDen a b j) b (row_den_positive a b j h.andE₂) (denominator_positive a b h)))

private theorem append_log_derivative (P f u v : PTm n)
    (hp : Γ ⊢[PRAAx] canonical P) (inverse : Γ ⊢[PRAAx] qmul f v ≐ qone) :
    Γ ⊢[PRAAx] qadd (qmul (qmul P u) f) P ≐ qmul (qmul P f) (qadd u v) := by
  let A := qmul P f
  have reorder : Γ ⊢[PRAAx] qmul (qmul P u) f ≐ qmul A u :=
    (qmul_associative P u f).eqTrans
      ((qmul_congr (.eqRefl _) (qmul_commutative u f)).eqTrans (qmul_associative P f u).eqSymm)
  have recover : Γ ⊢[PRAAx] qmul A v ≐ P :=
    (qmul_associative P f v).eqTrans ((qmul_congr (.eqRefl _) inverse).eqTrans (qmul_one_right P hp))
  exact (qadd_congr reorder recover.eqSymm).eqTrans (qmul_add A u v).eqSymm

def prefixLaw (a b j : PTm n) : Fm PTm n :=
  prefixDifference (arg a) (arg a) b j ≐
    qmul (differenceProduct (arg a) b j) (qsub qzero (positiveSum a b j))

@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (a b j : PTm n) :
    (prefixLaw a b j).subst σ = prefixLaw (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [prefixLaw]

private theorem law_zero (a b : PTm n) : Γ ⊢[PRAAx] prefixLaw a b zero := by
  have sum : Γ ⊢[PRAAx] positiveSum a b zero ≐ qzero :=
    GaussianRationalFiniteSum.sum_zero GaussianGammaNegativeCriticalCorrection.body (pairT a b)
  have negativeZero := (qsub_congr (.eqRefl qzero) sum).eqTrans (GaussianCoefficientNormOrder.qsub_self qzero)
  exact (GaussianGammaNegativeProductDerivative.prefix_zero _ _ _).eqTrans
    ((qmul_congr (.eqRefl (differenceProduct (arg a) b zero)) negativeZero).eqTrans (qmul_zero_right _)).eqSymm

private theorem law_succ (a b j : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (ih : Γ ⊢[PRAAx] prefixLaw a b j) : Γ ⊢[PRAAx] prefixLaw a b (succ j) := by
  let x := arg a
  let P := differenceProduct x b j
  let f := difference x b (succ j)
  let u := qsub qzero (positiveSum a b j)
  let v := qsub qzero (row a b j)
  have e : Γ ⊢[PRAAx] qadd u v ≐ qsub qzero (positiveSum a b (succ j)) :=
    (GaussianGammaDigammaSeriesTerms.subtract_add_exchange qzero (positiveSum a b j) qzero (row a b j)).eqTrans
      (qsub_congr (qzero_add qzero qzero_canonical) (GaussianGammaNegativeCriticalCorrection.prefix_succ a b j).eqSymm)
  exact (GaussianGammaNegativeProductDerivative.prefix_succ x x b j).eqTrans
    ((qadd_congr (qmul_congr ih (.eqRefl f)) (.eqRefl P)).eqTrans
      ((append_log_derivative P f u v (product_prefix_canonical x b j) (negative_factor_inverse a b j h)).eqTrans
        (qmul_congr (difference_succ x b j).eqSymm e)))

theorem prefix_coefficient (a b j : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx] prefixLaw a b j := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] guard (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using law_zero (Γ := Γ) a b
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        law_succ (Syn.shift a) (Syn.shift b) (var 0) hs.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem original_first_coefficient (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] firstCoefficient (arg a) b (succ N) ≐
      qmul (risingProduct (center (arg a) b (succ N)) b (succ (succ N))) (qnegative (correction a b N)) := by
  let j := succ N
  let x := arg a
  let P := differenceProduct x b j
  let f := fraction a b
  let u := qsub qzero (positiveSum a b j)
  let v := fraction b a
  have hb := denominator_positive a b h
  have sum : Γ ⊢[PRAAx] qadd u v ≐ qnegative (correction a b N) :=
    (qadd_commutative u v).eqTrans
      ((qadd_congr (.eqRefl v) (zero_minus (positiveSum a b j))).eqTrans
        (reversed_difference (positiveSum a b j) v).eqSymm)
  exact (qadd_congr (qmul_congr (prefix_coefficient a b j h) (.eqRefl f)) (.eqRefl P)).eqTrans
    ((append_log_derivative P f u v (product_prefix_canonical x b j) (reciprocal_fractions a b h.andE₁ hb)).eqTrans
      (qmul_congr (rising_product x b j hb).eqSymm sum))

theorem actual_negative_Gamma_shift_product_first_coefficient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶ firstCoefficient (arg (var 0)) (var 1) (succ (var 2)) ≐
        qmul (risingProduct (center (arg (var 0)) (var 1) (succ (var 2))) (var 1) (succ (succ (var 2))))
          (qnegative (correction (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (original_first_coefficient _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeCorrection
