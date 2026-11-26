import IPRADerivations.Analysis.Polynomials.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerAlgebra
import IPRADerivations.Analysis.Polynomials.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Analysis.Names.GaussianNameRingLaws

/-!
# Exact normalized inverse algebra for the Gamma quadratic expansion

All inverse identities use the actual normalized product inv*w=one.
The original rational square is identified for arbitrary raw input codes.
Only cancelling a final raw value requires that value to be canonical;
all intermediate sums and products are the original normalized outputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalInverseQuadraticAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul qzero canonical qmul_canonical qadd_represents canonical_unique represents_congr positive_product)
open GaussianRationalMetric (qsub qsub_represents)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr rescale_to)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalReciprocal (power power_zero power_succ)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalCoefficientScaling (qmul_add)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Even a raw noncanonical input has the exact normalized square. -/
theorem power_two_raw (w : PTm n) : Γ ⊢[PRAAx] power w two ≐ qmul w w := by
  have recode : Γ ⊢[PRAAx] GaussianFastValueCut.recode w ≐ GaussianTranslatedNonconstant.recode w :=
    canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical w) (GaussianTranslatedNonconstant.recode_canonical w)
      (raw_den_positive w) (GaussianFastValueCut.recode_represents w) (GaussianTranslatedNonconstant.recode_represents w)
  have first : Γ ⊢[PRAAx] power w one ≐ GaussianFastValueCut.recode w :=
    (power_succ w zero).eqTrans ((qmul_congr (power_zero w) (.eqRefl _)).eqTrans
      ((qmul_commutative qone w).eqTrans (GaussianNameRingLaws.multiply_one_recode w)))
  exact (power_succ w one).eqTrans ((qmul_congr (first.eqTrans recode) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticCoefficientValues.qmul_recode_left w w))

theorem cancel_nested_product (inv w y : PTm n) (hy : Γ ⊢[PRAAx] canonical y)
    (hi : Γ ⊢[PRAAx] qmul inv w ≐ qone) : Γ ⊢[PRAAx] qmul inv (qmul w y) ≐ y :=
  (qmul_associative inv w y).eqSymm.eqTrans ((qmul_congr hi (.eqRefl _)).eqTrans
    ((qmul_commutative qone y).eqTrans (GaussianReciprocalHorner.qmul_one_right y hy)))

theorem inverse_quadratic (inv w c : PTm n) (hi : Γ ⊢[PRAAx] qmul inv w ≐ qone) : Γ ⊢[PRAAx]
    qmul inv (qadd w (qmul c (qmul w w))) ≐ qadd qone (qmul w c) := by
  have inner : Γ ⊢[PRAAx] qmul c (qmul w w) ≐ qmul w (qmul w c) :=
    (qmul_commutative c (qmul w w)).eqTrans (qmul_associative w w c)
  have second := (qmul_congr (.eqRefl inv) inner).eqTrans
    (cancel_nested_product inv w (qmul w c) (qmul_canonical w c) hi)
  exact (qmul_add inv w (qmul c (qmul w w))).eqTrans (qadd_congr hi second)

/-- This version binds the literal power term of the original sampler. -/
theorem inverse_quadratic_power (inv w c : PTm n) (hi : Γ ⊢[PRAAx] qmul inv w ≐ qone) : Γ ⊢[PRAAx]
    qmul inv (qadd w (qmul c (power w two))) ≐ qadd qone (qmul w c) :=
  (qmul_congr (.eqRefl inv) (qadd_congr (.eqRefl w) (qmul_congr (.eqRefl c) (power_two_raw w)))).eqTrans
    (inverse_quadratic inv w c hi)

theorem inverse_affine_difference (inv w g c : PTm n) (hc : Γ ⊢[PRAAx] canonical c)
    (hi : Γ ⊢[PRAAx] qmul inv w ≐ qone) : Γ ⊢[PRAAx]
    qmul inv (qadd (qsub g qone) (qmul w c)) ≐ qadd (qmul inv (qsub g qone)) c :=
  (qmul_add inv (qsub g qone) (qmul w c)).eqTrans (qadd_congr (.eqRefl _) (cancel_nested_product inv w c hc hi))

/-- Associativity of normalized subtraction, even for three raw codes. -/
theorem subtract_sum (x y b : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub x y) b ≐ qsub x (qadd y b) := by
  let E := rawDen x*rawDen y*rawDen b
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (positive_product _ _ (raw_den_positive x) (raw_den_positive y)) (raw_den_positive b)
  have hx := rescale_to x (rawGaussian x) (rawDen x) (rawDen y*rawDen b) E (raw_represents (Γ := Γ) x) (by dsimp only [E]; ipra_ring)
  have hy := rescale_to y (rawGaussian y) (rawDen y) (rawDen x*rawDen b) E (raw_represents (Γ := Γ) y) (by dsimp only [E]; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen x*rawDen y) E (raw_represents (Γ := Γ) b) (by dsimp only [E]; ipra_ring)
  have left := qsub_represents _ _ _ _ E hE (qsub_represents _ _ _ _ E hE hx hy) hb
  have right := qsub_represents _ _ _ _ E hE hx (qadd_represents _ _ _ _ _ hE hy hb)
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _) (GaussianRationalMetric.qsub_canonical _ _) hE (hrv := right)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) left
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ring

theorem subtract_one_sum (p b : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub p qone) b ≐ qsub p (qadd qone b) := subtract_sum p qone b

theorem subtract_zero_difference (a c : PTm n) : Γ ⊢[PRAAx]
    qsub a (qsub qzero c) ≐ qadd a c := by
  let E := rawDen a*rawDen c
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive a) (raw_den_positive c)
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen c) E (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hc := rescale_to c (rawGaussian c) (rawDen c) (rawDen a) E (raw_represents (Γ := Γ) c) (by dsimp only [E]; ipra_ring)
  have left := qsub_represents _ _ _ _ E hE ha (qsub_represents _ _ _ _ E hE (GaussianRationalHorner.zero_represents E) hc)
  have right := qadd_represents _ _ _ _ _ hE ha hc
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _) (GaussianRationalHorner.qadd_canonical _ _) hE (hrv := right)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) left
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero] <;> ring

theorem actual_inverse_nested_product_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((canonical (var 2) ⋏ qmul (var 0) (var 1) ≐ qone) ⟶ qmul (var 0) (qmul (var 1) (var 2)) ≐ var 2) :=
  closeUniv 3 (.impI (cancel_nested_product _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_inverse_original_quadratic_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((qmul (var 0) (var 1) ≐ qone) ⟶
      qmul (var 0) (qadd (var 1) (qmul (var 2) (power (var 1) two))) ≐ qadd qone (qmul (var 1) (var 2))) :=
  closeUniv 3 (.impI (inverse_quadratic_power _ _ _ Prf.hyp0))

theorem actual_inverse_affine_difference_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((canonical (var 3) ⋏ qmul (var 0) (var 1) ≐ qone) ⟶
      qmul (var 0) (qadd (qsub (var 2) qone) (qmul (var 1) (var 3))) ≐ qadd (qmul (var 0) (qsub (var 2) qone)) (var 3)) :=
  closeUniv 4 (.impI (inverse_affine_difference _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_raw_subtract_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qsub (qsub (var 0) (var 1)) (var 2) ≐ qsub (var 0) (qadd (var 1) (var 2))) :=
  closeUniv 3 (subtract_sum _ _ _)

theorem actual_raw_subtract_zero_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qsub (var 0) (qsub qzero (var 1)) ≐ qadd (var 0) (var 1)) :=
  closeUniv 2 (subtract_zero_difference _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalInverseQuadraticAlgebra
