import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaLocalPoleGuards
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaRepeatedShift

/-!
# Exact finite factors at a negative integer

The actual products of h/B-j and of 1-(h/B)/j retain their original
Gaussian rational factor values. Factoring -j from each factor yields
the exact signed factorial multiplier at every numerical n.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleFiniteFactors

open_ipra
open GaussianGammaLocalPoleGuards (center)
open GaussianGammaPoleZeros (poleNumerator)
open GaussianGammaRepeatedShift (linearBody risingProduct linear_at prefix_zero prefix_succ)
open GaussianGammaEulerHeadShift (linear)
open GaussianGammaEulerHeadLower (translated translated_zero)
open GaussianRationalFiniteProduct (qprod product_zero product_succ)
open GaussianRationalHorner
  (ofGaussian ofGaussian_canonical ofGaussian_represents qmul qmul_canonical qmul_represents
    canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr rescale_to)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalReciprocal (power power_zero power_succ)
open GaussianRationalPowerAlgebra (qmul_shuffle qmul_commutative)
open GaussianRationalMatrixFiniteSums (minusOne)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_neg im_neg re_mul im_mul re_scale im_scale re_one im_one)
open ComplexLogarithmRemainder (scale oneCode)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def difference (h B j : PTm n) : PTm n := ofGaussian (center h B j) B
def factor (h B j : PTm n) : PTm n := ofGaussian (ComplexLogarithmRemainder.neg (center h B j)) (B*j)
def negativeIndex (j : PTm n) : PTm n := ofGaussian (poleNumerator one j) one
def differenceBody : PTm 2 := difference (fstT (var 1)) (sndT (var 1)) (succ (var 0))
def factorBody : PTm 2 := factor (fstT (var 1)) (sndT (var 1)) (succ (var 0))
def differenceProduct (h B j : PTm n) : PTm n := qprod differenceBody j (pairT h B)
def factorProduct (h B j : PTm n) : PTm n := qprod factorBody j (pairT h B)
def signedFactorial (j : PTm n) : PTm n := qmul (power minusOne j) (naturalPoint (fact j))

ipra_subst difference
ipra_subst factor
ipra_subst differenceProduct
ipra_subst factorProduct
ipra_subst signedFactorial [fact]

theorem factor_identity (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] difference h B j ≐ qmul (negativeIndex j) (factor h B j) := by
  let a := center h B j
  let k := poleNumerator one j
  let b := ComplexLogarithmRemainder.neg a
  let D := B*j
  have hD := positive_product _ _ hB hj
  have old := rescale_to (difference h B j) a B j D (ofGaussian_represents a B hB) (.eqRefl _)
  have prod := qmul_represents (negativeIndex j) (factor h B j) k b one D (le_refl one) hD
    (ofGaussian_represents k one (le_refl one)) (ofGaussian_represents b D hD)
  have same : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul k b) (scale j a) := by
    apply equal_of_values <;>
      simp only [k,b,poleNumerator,re_mul,im_mul,re_neg,im_neg,re_scale,im_scale,re_one,im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ D (ofGaussian_canonical _ _ hB) (qmul_canonical _ _) hD old
    (represents_congr (.eqRefl _) same (one_mul _) prod)

private theorem negativeIndex_value (j : PTm n) : Γ ⊢[PRAAx]
    negativeIndex j ≐ qmul minusOne (naturalPoint j) := by
  let a := scale j oneCode
  have same : Γ ⊢[PRAAx] equal (poleNumerator one j) (ComplexLogarithmRemainder.neg a) := by
    apply equal_of_values <;> simp only [a,poleNumerator,re_neg,im_neg,re_scale,im_scale] <;>
      ipra_simps <;> ring
  have eq : Γ ⊢[PRAAx] negativeIndex j ≐ qnegative (naturalPoint j) :=
    canonical_unique _ _ _ one (ofGaussian_canonical _ _ (le_refl one)) (qnegative_canonical _) (le_refl _)
      (represents_congr (.eqRefl _) same (.eqRefl _) (ofGaussian_represents _ _ (le_refl one)))
      (qnegative_represents _ _ _ (natural_point_represents j))
  exact eq.eqTrans (GaussianRationalMatrixFiniteSums.negative_as_minusOne _)

private theorem naturalPoint_mul (a b : PTm n) : Γ ⊢[PRAAx]
    qmul (naturalPoint a) (naturalPoint b) ≐ naturalPoint (a*b) := by
  have raw := qmul_represents (naturalPoint a) (naturalPoint b) (scale a oneCode) (scale b oneCode) one one
    (le_refl (Γ := Γ) one) (le_refl one) (natural_point_represents a) (natural_point_represents b)
  have same : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul (scale a oneCode) (scale b oneCode))
      (scale (a*b) oneCode) := by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ one (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one)) (le_refl _)
    (represents_congr (.eqRefl _) same (one_mul _) raw) (natural_point_represents (a*b))

private theorem naturalPoint_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] naturalPoint a ≐ naturalPoint b := by
  ipra_congr (naturalPoint (var 0) : PTm 1) with [h]

theorem signedFactorial_zero : Γ ⊢[PRAAx] signedFactorial (zero : PTm n) ≐ qone := by
  have factEq := naturalPoint_congr (fact_zero (Γ := Γ) zero)
  have nEq : Γ ⊢[PRAAx] naturalPoint (one : PTm n) ≐ qone := by
    have same : Γ ⊢[PRAAx] equal (scale one oneCode) oneCode := by
      apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
    exact canonical_unique _ _ _ one (ofGaussian_canonical _ _ (le_refl _)) qone_canonical (le_refl _)
      (represents_congr (.eqRefl _) same (.eqRefl _) (natural_point_represents one))
      (ofGaussian_represents _ _ (le_refl _))
  exact (qmul_congr (power_zero minusOne) (factEq.eqTrans nEq)).eqTrans (qmul_one_right _ qone_canonical)

theorem signedFactorial_succ (j : PTm n) : Γ ⊢[PRAAx]
    signedFactorial (succ j) ≐ qmul (signedFactorial j) (negativeIndex (succ j)) := by
  have q := (naturalPoint_mul (Γ := Γ) (fact j) (succ j)).eqTrans
    (naturalPoint_congr (fact_succ j zero).eqSymm)
  exact (qmul_congr (power_succ minusOne j) q.eqSymm).eqTrans
    ((qmul_shuffle (power minusOne j) minusOne (naturalPoint (fact j)) (naturalPoint (succ j))).eqTrans
      (qmul_congr (.eqRefl _) (negativeIndex_value _).eqSymm))

private theorem difference_at (h B j : PTm n) : Γ ⊢[PRAAx]
    inst2 differenceBody j (pairT h B) ≐ difference h B (succ j) := by
  ipra_congr (difference (var 0) (var 1) (succ (var 2)) : PTm 3) with
    [fst_pair _ _, snd_pair _ _, .eqRefl j] using [differenceBody, inst2]

theorem factor_at (h B j : PTm n) : Γ ⊢[PRAAx]
    inst2 factorBody j (pairT h B) ≐ factor h B (succ j) := by
  ipra_congr (factor (var 0) (var 1) (succ (var 2)) : PTm 3) with
    [fst_pair _ _, snd_pair _ _, .eqRefl j] using [factorBody, inst2]

theorem difference_succ (h B j : PTm n) : Γ ⊢[PRAAx]
    differenceProduct h B (succ j) ≐ qmul (differenceProduct h B j) (difference h B (succ j)) :=
  (product_succ differenceBody j (pairT h B)).eqTrans (qmul_congr (.eqRefl _) (difference_at h B j))

theorem factor_succ (h B j : PTm n) : Γ ⊢[PRAAx]
    factorProduct h B (succ j) ≐ qmul (factorProduct h B j) (factor h B (succ j)) :=
  (product_succ factorBody j (pairT h B)).eqTrans (qmul_congr (.eqRefl _) (factor_at h B j))

def productLaw (h B j : PTm n) : Fm PTm n :=
  differenceProduct h B j ≐ qmul (signedFactorial j) (factorProduct h B j)

ipra_subst productLaw

theorem productLaw_zero (h B : PTm n) : Γ ⊢[PRAAx] productLaw h B zero :=
  (product_zero differenceBody (pairT h B)).eqTrans
    ((qmul_congr signedFactorial_zero (product_zero factorBody (pairT h B))).eqTrans
      (qmul_one_right _ qone_canonical)).eqSymm

theorem productLaw_succ (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] productLaw h B j) : Γ ⊢[PRAAx] productLaw h B (succ j) := by
  exact (difference_succ h B j).eqTrans ((qmul_congr ih (factor_identity h B (succ j) hB (zero_lt_succ j))).eqTrans
    ((qmul_shuffle (signedFactorial j) (factorProduct h B j) (negativeIndex (succ j)) (factor h B (succ j))).eqTrans
      (qmul_congr (signedFactorial_succ j).eqSymm (factor_succ h B j).eqSymm)))

theorem finite_pole_factors (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] productLaw h B j := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (productLaw (Syn.shift h) (Syn.shift B) (var 0)) := by
    ipra_qfind [subst_productLaw]
    · exact productLaw_zero h B
    · exact productLaw_succ _ _ _ bs.wk Prf.hyp0
  simpa only [subst_productLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem original_finite_pole_factors_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ productLaw (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (finite_pole_factors _ _ _ Prf.hyp0))

private theorem first_linear (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] linear (center h B j) B zero ≐ difference h B j :=
  canonical_unique _ _ _ B (ofGaussian_canonical _ _ hB) (ofGaussian_canonical _ _ hB) hB
    (represents_congr (.eqRefl _) (translated_zero (center h B j) B) (.eqRefl _)
      (ofGaussian_represents _ _ hB)) (ofGaussian_represents _ _ hB)

private theorem successive_center_terms (h B j i : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] linear (center h B (succ j)) B (one+i) ≐ linear (center h B j) B i := by
  have same : Γ ⊢[PRAAx] equal (translated (center h B (succ j)) B (one+i))
      (translated (center h B j) B i) := by
    apply equal_of_values <;>
      simp only [center,translated,poleNumerator,re_add,im_add,re_neg,im_neg,re_scale,im_scale,re_one,im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ B (ofGaussian_canonical _ _ hB) (ofGaussian_canonical _ _ hB) hB
    (represents_congr (.eqRefl _) same (.eqRefl _) (ofGaussian_represents _ _ hB))
    (ofGaussian_represents _ _ hB)

private theorem offset_terms (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (offB linearBody) linearBody j
      (pairT one (GaussianGammaShiftTrajectory.data (center h B (succ j)) B))
      (GaussianGammaShiftTrajectory.data (center h B j) B) := by
  refine .allI (.impI ?_)
  let H := Syn.shift h
  let C := Syn.shift B
  let J := Syn.shift j
  have b : Γ.map Fm.shift ⊢[PRAAx] le one C := by simpa [C,Fm.shift,Syn.shift] using hB.shift
  have e := GaussianRationalFiniteProduct.offset_at (Γ := lt (var 0) (Syn.shift j) :: Γ.map Fm.shift)
    linearBody one (var 0)
    (GaussianGammaShiftTrajectory.data (center H C (succ J)) C)
  have p := e.eqTrans ((linear_at (center H C (succ J)) C (one+var 0)).eqTrans
    ((successive_center_terms H C J (var 0) b.wk).eqTrans (linear_at (center H C J) C (var 0)).eqSymm))
  simpa only [Syn.shift,subst_pairT,GaussianGammaShiftTrajectory.subst_data,GaussianGammaLocalPoleGuards.subst_center,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,C,H,J] using p

theorem rising_reverse_step (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] risingProduct (center h B (succ j)) B (succ j) ≐
      qmul (difference h B (succ j)) (risingProduct (center h B j) B j) := by
  let u := center h B (succ j)
  let v := center h B j
  let D := GaussianGammaShiftTrajectory.data u B
  have e : Γ ⊢[PRAAx] succ j ≐ one+j := by ipra_ring
  have split := (GaussianRationalFiniteProduct.product_index_congr linearBody e (.eqRefl D)).eqTrans
    (GaussianRationalFiniteProduct.product_split linearBody one j D)
  have first := (prefix_succ u B zero).eqTrans
    ((qmul_congr (prefix_zero u B) (first_linear h B (succ j) hB)).eqTrans
      ((qmul_commutative _ _).eqTrans (qmul_one_right _ (ofGaussian_canonical _ _ hB))))
  have rest := GaussianRationalFiniteProduct.product_congr_bounded (offB linearBody) linearBody j
    (pairT one D) (GaussianGammaShiftTrajectory.data v B) (offset_terms h B j hB)
  exact split.eqTrans (qmul_congr first rest)

def reversal (h B j : PTm n) : Fm PTm n :=
  risingProduct (center h B j) B j ≐ differenceProduct h B j

ipra_subst reversal

theorem reverse_rising (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] reversal h B j := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (reversal (Syn.shift h) (Syn.shift B) (var 0)) := by
    ipra_qfind [subst_reversal]
    · exact (prefix_zero (center h B zero) B).eqTrans (product_zero differenceBody (pairT h B)).eqSymm
    · exact (rising_reverse_step _ _ _ bs.wk).eqTrans ((qmul_congr (.eqRefl _) Prf.hyp0).eqTrans
        ((qmul_commutative _ _).eqTrans (difference_succ _ _ _).eqSymm))
  simpa only [subst_reversal,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem centered_rising_factorization (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] risingProduct (center h B j) B (succ j) ≐
      qmul (ofGaussian h B) (qmul (signedFactorial j) (factorProduct h B j)) := by
  have last : Γ ⊢[PRAAx] linear (center h B j) B j ≐ ofGaussian h B :=
    canonical_unique _ _ _ B (ofGaussian_canonical _ _ hB) (ofGaussian_canonical _ _ hB) hB
      (represents_congr (.eqRefl _) (GaussianGammaLocalPoleGuards.translation_at_center h B j)
        (.eqRefl _) (ofGaussian_represents _ _ hB)) (ofGaussian_represents _ _ hB)
  exact (prefix_succ _ B j).eqTrans ((qmul_congr
    ((reverse_rising h B j hB).eqTrans (finite_pole_factors h B j hB)) last).eqTrans (qmul_commutative _ _))

theorem actual_C24_rising_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ risingProduct (center (var 0) (var 1) (var 2)) (var 1) (succ (var 2)) ≐
      qmul (ofGaussian (var 0) (var 1)) (qmul (signedFactorial (var 2)) (factorProduct (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (centered_rising_factorization _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleFiniteFactors
