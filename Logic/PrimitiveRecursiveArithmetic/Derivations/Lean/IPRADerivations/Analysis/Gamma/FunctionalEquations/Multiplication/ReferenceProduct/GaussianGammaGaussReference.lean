import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ShiftedProducts.GaussianGammaGaussDomain

/-!
# The reference arguments in Gauss multiplication

The normalization point (1/m) gives the rows ((r+1)/m).
Each row lies in the unit disk and has a uniform pole margin (1/m).
The exact difference of a row at (z/B) and its reference row
is independent of (r).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReference

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (bounded scale normSq normSq_scale normSq_one oneCode)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard)
open GaussianGammaReciprocalInverse (source)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents positive_product qadd qadd_represents
  qadd_canonical represents_congr represents_rescale canonical_unique)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents qnegative qnegative_canonical qnegative_represents)
open GaussianRationalNaturalScale (natScale natScale_represents natScale_canonical)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRootAlgebra (sub equal_of_values equal_refl normSq_equal re_add im_add re_scale im_scale
  re_sub im_sub re_neg im_neg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem scaled_one_norm (r : PTm n) : Γ ⊢[PRAAx] normSq (scale r oneCode) ≐ r*r :=
  (normSq_scale r oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))

theorem reference_pole_at (r m j : PTm n) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] poleAt (scale r oneCode) m one m j := by
  have shape : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (translated (scale r oneCode) m j) (scale (r+m*j) oneCode) := by
    apply equal_of_values <;> simp only [translated,re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring
  have norm := (normSq_equal shape).eqTrans (scaled_one_norm (r+m*j))
  have one_le_index := le_trans hr (le_add_right r (m*j))
  have sq := le_mul_mono (le_refl (m*m)) (le_mul_mono one_le_index one_le_index)
  exact le_congr (by ipra_ring)
    (congrMul (.eqRefl _) norm.eqSymm) sq

theorem reference_source (r m : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] source (scale r oneCode) one m one m := by
  have hM := le_trans hr hm
  have radius : Γ ⊢[PRAAx] bounded (scale r oneCode) (one*m) :=
    le_congr (scaled_one_norm r).eqSymm (by ipra_ring) (le_mul_mono hm hm)
  refine .andI (.andI (le_refl one) (.andI hM radius)) (.andI (le_refl one) (.andI hM ?_))
  refine .allI (.impI ?_)
  have hr' : le (var 0) (two*one) :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift r) := by
    simpa [Fm.shift,Syn.shift,one] using hr.shift.wk
  simpa [poleGuard,Syn.shift,one,two] using reference_pole_at (Syn.shift r) (Syn.shift m) (var 0) hr'

theorem shifted_reference_source (r m : PTm n) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] source (scale (succ r) oneCode) one m one m :=
  reference_source (succ r) m (zero_lt_succ r) hr

def offset (z B m : PTm n) : PTm n := ofGaussian (sub (scale m z) (scale B oneCode)) (B*m)

theorem row_offset (z B m r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qsub (ofGaussian (shiftedNumerator z B m r) (B*m)) (ofGaussian (scale (succ r) oneCode) m) ≐
      offset z B m := by
  let a := shiftedNumerator z B m r
  let b := scale (succ r) oneCode
  let D := B*m
  let q := ofGaussian a D
  let v := ofGaussian b m
  have hD := positive_product B m hB hm
  have lhs := qsub_represents q v a (scale B b) D hD (ofGaussian_represents _ _ hD)
    (represents_congr (.eqRefl _) (equal_refl _) (mul_comm _ _) (represents_rescale v b m B (ofGaussian_represents _ _ hm)))
  have equals : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (sub a (scale B b)) (sub (scale m z) (scale B oneCode)) := by
    apply equal_of_values <;>
      simp only [a,b,shiftedNumerator,translated,re_add,im_add,re_sub,im_sub,re_scale,im_scale] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (qsub_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) equals (.eqRefl _) lhs) (ofGaussian_represents _ _ hD)

theorem negative_row_sum (z B m r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qnegative (ofGaussian (shiftedNumerator z B m r) (B*m)) ≐
      qadd (qnegative (ofGaussian (scale (succ r) oneCode) m)) (qnegative (offset z B m)) := by
  let A := shiftedNumerator z B m r
  let W := scale (succ r) oneCode
  let C := sub (scale m z) (scale B oneCode)
  let D := B*m
  let q := ofGaussian W m
  let x := offset z B m
  have hD := positive_product B m hB hm
  have hq := represents_congr (.eqRefl _) (equal_refl _) (mul_comm _ _)
    (represents_rescale q W m B (ofGaussian_represents _ _ hm))
  have hx := ofGaussian_represents C D hD
  have lhs := qnegative_represents (ofGaussian A D) A D (ofGaussian_represents _ _ hD)
  have rhs := qadd_represents (qnegative q) (qnegative x)
    (ComplexLogarithmRemainder.neg (scale B W)) (ComplexLogarithmRemainder.neg C) D hD
    (qnegative_represents _ _ _ hq) (qnegative_represents _ _ _ hx)
  have value : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.neg A)
      (ComplexLogarithmRemainder.add (ComplexLogarithmRemainder.neg (scale B W)) (ComplexLogarithmRemainder.neg C)) := by
    apply equal_of_values <;>
      simp only [A,W,C,shiftedNumerator,translated,re_add,im_add,re_sub,im_sub,re_neg,im_neg,re_scale,im_scale] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (qnegative_canonical _) (qadd_canonical _ _) hD
    (represents_congr (.eqRefl _) value (.eqRefl _) lhs) rhs

theorem scaled_offset (z B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] natScale m (offset z B m) ≐ qsub (ofGaussian (scale m z) B) qone := by
  let w := scale m z
  let c := sub w (scale B oneCode)
  let hD := positive_product B m hB hm
  have lhs := natScale_represents m (offset z B m) c (B*m) hD (ofGaussian_represents _ _ hD)
  have rhs := qsub_represents (ofGaussian w B) qone w (scale B oneCode) B hB
    (ofGaussian_represents _ _ hB) (qone_represents_scaled B)
  exact canonical_unique _ _ _ _ (natScale_canonical _ _) (qsub_canonical _ _) hD lhs
    (represents_rescale _ _ _ _ rhs)

theorem original_Gauss_reference_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 0) (var 1) ⟶ source (scale (succ (var 0)) oneCode) one (var 1) one (var 1)) :=
  closeUniv 2 (.impI (shifted_reference_source _ _ Prf.hyp0))

theorem original_Gauss_reference_row_offset_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶
      qsub (ofGaussian (shiftedNumerator (var 0) (var 1) (var 2) (var 3)) (var 1*var 2))
        (ofGaussian (scale (succ (var 3)) oneCode) (var 2)) ≐ offset (var 0) (var 1) (var 2)) :=
  closeUniv 4 (.impI (.impI (row_offset _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_Gauss_reference_exponent_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶
      (qnegative (ofGaussian (shiftedNumerator (var 0) (var 1) (var 2) (var 3)) (var 1*var 2)) ≐
        qadd (qnegative (ofGaussian (scale (succ (var 3)) oneCode) (var 2)))
          (qnegative (offset (var 0) (var 1) (var 2)))) ⋏
      (natScale (var 2) (offset (var 0) (var 1) (var 2)) ≐ qsub (ofGaussian (scale (var 2) (var 0)) (var 1)) qone)) :=
  closeUniv 4 (.impI (.impI (.andI (negative_row_sum _ _ _ _ Prf.hyp1 Prf.hyp0)
    (scaled_offset _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReference
