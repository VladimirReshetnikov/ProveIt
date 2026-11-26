import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSquareCancellation
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentExponentialPeriod

/-!
# A quantitative fourth-root branch at one

A Gaussian rational within 21/16 of one is separated from the three
other fourth roots by at least 1/16. The exact factorization of its
fourth power minus one then gives a linear branch recovery estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianRationalFourthRootBranch

open_ipra
open ComplexLogarithmRemainder (normSq normSq_eval oneCode eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryPoint imaginaryCode)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalHorner (qmul qadd canonical positive_product ofGaussian_represents ofGaussian_canonical
  represents canonical_unique represents_congr)
open GaussianRationalLowerBounds (lower lower_congr product_lower inverse_bound name_lower)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative qnegative_represents qsub_represents
  bounded_difference_iff qsub_canonical qnegative_canonical)
open GaussianRationalReciprocal (qone reciprocal reciprocal_identity bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianRationalSyntheticDivision (qone_canonical qmul_congr qsub_congr qadd_congr)
open GaussianRationalSquareCancellation (difference_factorization)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRootAlgebra (sub re_sub im_sub re_neg im_neg re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem sixteen_positive : Γ ⊢[PRAAx] le one (num 16 : PTm n) := by ipra_le 15

private theorem separate (q s b : PTm n)
    (hb : Γ ⊢[PRAAx] represents s b one)
    (hn : Γ ⊢[PRAAx] le two (normSq (sub oneCode b)))
    (hq : Γ ⊢[PRAAx] distanceBounded q qone (num 21) (num 16)) :
    Γ ⊢[PRAAx] lower (qsub q s) one (num 16) := by
  refine .orE (RationalArgmin.total (GaussianRationalMetric.squaredTolerance one (num 16))
    (GaussianRationalMetric.qnormSq (qsub q s))) Prf.hyp0 ?_
  let Δ := bounded (qsub q s) one (num 16) :: Γ
  have hs : Δ ⊢[PRAAx] distanceBounded q s one (num 16) := Prf.hyp0
  have hd : Δ ⊢[PRAAx] le one (num 16 : PTm n) := sixteen_positive
  have both := GaussianReconstructionRoots.distance_triangle qone q s (num 21) (num 16) one (num 16)
    hd hd (distance_symmetric _ _ _ _ hd hq.wk) hs
  have near : Δ ⊢[PRAAx] distanceBounded qone s (num 22) (num 16) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd hd) hd
      (le_of_eq_add (d := zero) (by ipra_ring)) both
  have actual := (bounded_difference_iff qone s oneCode b one (num 22) (num 16)
    (le_refl _) hd (ofGaussian_represents oneCode one (le_refl one)) hb.wk).iffMp near
  have bad : Δ ⊢[PRAAx] le (num 512) (num 484) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (num 16*num 16)) hn.wk) actual)
  exact not_succ_le_self (num 484) _ (le_trans (by ipra_le 27) bad)

private theorem negative_one_norm : Γ ⊢[PRAAx] le two (normSq (sub oneCode (ComplexLogarithmRemainder.neg oneCode) : PTm n)) := by
  have e : Γ ⊢[PRAAx] normSq (sub oneCode (ComplexLogarithmRemainder.neg oneCode) : PTm n) ≐ num 4 := by
    apply deriveNat
    rw [normSq_eval]
    simp only [re_sub,im_sub,re_neg,im_neg,re_one,im_one]
    ipra_simps
    ring
  exact le_congr (.eqRefl _) e.eqSymm (by ipra_le 2)

private theorem imaginary_norm : Γ ⊢[PRAAx] le two (normSq (sub oneCode imaginaryCode : PTm n)) := by
  apply le_congr (.eqRefl _) _ (le_refl two)
  apply deriveNat
  rw [normSq_eval]
  simp only [re_sub,im_sub,re_one,im_one,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem negative_imaginary_norm : Γ ⊢[PRAAx] le two (normSq (sub oneCode (ComplexLogarithmRemainder.neg imaginaryCode) : PTm n)) := by
  apply le_congr (.eqRefl _) _ (le_refl two)
  apply deriveNat
  rw [normSq_eval]
  simp only [re_sub,im_sub,re_neg,im_neg,re_one,im_one,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem subtract_negative (q s : PTm n) (hs : Γ ⊢[PRAAx] canonical s) :
    Γ ⊢[PRAAx] qsub q (qnegative s) ≐ qadd q s :=
  qadd_congr (.eqRefl _) (GaussianDeterminantSignTransport.negative_involution s hs)

private theorem imaginary_squared :
    Γ ⊢[PRAAx] qmul (imaginaryPoint : PTm n) imaginaryPoint ≐ qnegative qone := by
  let s : PTm n := GaussianArctangentExponentialPeriod.minusOneCode
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal s (ComplexLogarithmRemainder.neg oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [s,GaussianArctangentExponentialPeriod.minusOneCode,eval_re_code,eval_im_code,
        ZT.toZ_sub,ZT.toZ_ofNat,re_neg,im_neg,re_one,im_one] <;> ipra_simps <;> ring
  exact GaussianArctangentExponentialPeriod.imaginary_square.eqTrans
    (canonical_unique _ _ _ one (ofGaussian_canonical _ _ (le_refl one)) (qnegative_canonical _) (le_refl one)
      (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ (le_refl one)))
      (qnegative_represents _ _ _ (ofGaussian_represents oneCode one (le_refl one))))

private theorem square_plus_one (q : PTm n) :
    Γ ⊢[PRAAx] qadd (qmul q q) qone ≐ qmul (qsub q imaginaryPoint) (qadd q imaginaryPoint) :=
  (subtract_negative _ _ qone_canonical).eqSymm.eqTrans
    ((qsub_congr (.eqRefl _) imaginary_squared.eqSymm).eqTrans (difference_factorization q imaginaryPoint))

private theorem extra_factors_lower (q : PTm n) (hq : Γ ⊢[PRAAx] distanceBounded q qone (num 21) (num 16)) :
    Γ ⊢[PRAAx] lower (qmul (qadd q qone) (qadd (qmul q q) qone)) one (num 4096) := by
  let i : PTm n := imaginaryPoint
  have ir := ofGaussian_represents (Γ := Γ) imaginaryCode one (le_refl one)
  have ic := ofGaussian_canonical (Γ := Γ) imaginaryCode one (le_refl one)
  have lo₁ := separate q (qnegative qone) (ComplexLogarithmRemainder.neg oneCode)
    (qnegative_represents _ _ _ (ofGaussian_represents oneCode one (le_refl one))) negative_one_norm hq
  have loᵢ := separate q i imaginaryCode ir imaginary_norm hq
  have loₙ := separate q (qnegative i) (ComplexLogarithmRemainder.neg imaginaryCode)
    (qnegative_represents _ _ _ ir) negative_imaginary_norm hq
  have loPlusOne := lower_congr (subtract_negative q qone qone_canonical) (.eqRefl _) (.eqRefl _) lo₁
  have loPlusI := lower_congr (subtract_negative q i ic) (.eqRefl _) (.eqRefl _) loₙ
  have pair := lower_congr (square_plus_one q).eqSymm (.eqRefl _) (.eqRefl _)
    (product_lower _ _ _ _ _ _ sixteen_positive sixteen_positive loᵢ loPlusI)
  exact lower_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (product_lower _ _ _ _ _ _ sixteen_positive (positive_product _ _ sixteen_positive sixteen_positive) loPlusOne pair)

/-- Exact finite branch recovery, with an error linear in the fourth-power
residual rather than a choice of a nearby root. -/
theorem cancel_fourth (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hNear : Γ ⊢[PRAAx] distanceBounded q qone (num 21) (num 16))
    (hFourth : Γ ⊢[PRAAx] distanceBounded (qmul (qmul q q) (qmul q q)) qone A B) :
    Γ ⊢[PRAAx] distanceBounded q qone (num 4096*A) B := by
  let r := qmul q q
  let S := qmul (qadd q qone) (qadd r qone)
  let d := qsub q qone
  let v := reciprocal S
  have hp : Γ ⊢[PRAAx] le one (num 4096 : PTm n) := by ipra_le 4095
  have lo := extra_factors_lower q hNear
  have inv := inverse_bound S one (num 4096) (le_refl _) hp lo
  have eq := reciprocal_identity S
    (GaussianNameReciprocal.lower_norm_positive S (num 4096) hp (name_lower _ _ _ (le_refl _) hp lo))
  have sq₁ : Γ ⊢[PRAAx] qsub (qmul r r) qone ≐ qmul (qsub r qone) (qadd r qone) :=
    (qsub_congr (.eqRefl _) (qmul_one_right qone qone_canonical).eqSymm).eqTrans (difference_factorization r qone)
  have sq₂ : Γ ⊢[PRAAx] qsub r qone ≐ qmul d (qadd q qone) :=
    (qsub_congr (.eqRefl _) (qmul_one_right qone qone_canonical).eqSymm).eqTrans (difference_factorization q qone)
  have factor : Γ ⊢[PRAAx] qsub (qmul r r) qone ≐ qmul d S :=
    sq₁.eqTrans ((qmul_congr sq₂ (.eqRefl _)).eqTrans (qmul_associative _ _ _))
  have raw := bound_congr factor (.eqRefl _) (.eqRefl _) hFourth
  have rest := bounded_product _ _ _ _ _ _ hB (le_refl one) raw inv
  have cancel : Γ ⊢[PRAAx] qmul (qmul d S) v ≐ d :=
    (qmul_associative _ _ _).eqTrans ((qmul_congr (.eqRefl _) eq).eqTrans (qmul_one_right d (qsub_canonical _ _)))
  exact bound_congr cancel (by ipra_ring) (by ipra_ring) rest

theorem actual_rational_fourth_root_branch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ distanceBounded (var 0) qone (num 21) (num 16) ⟶
      distanceBounded (qmul (qmul (var 0) (var 0)) (qmul (var 0) (var 0))) qone (var 1) (var 2) ⟶
        distanceBounded (var 0) qone (num 4096*var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (cancel_fourth _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalFourthRootBranch
