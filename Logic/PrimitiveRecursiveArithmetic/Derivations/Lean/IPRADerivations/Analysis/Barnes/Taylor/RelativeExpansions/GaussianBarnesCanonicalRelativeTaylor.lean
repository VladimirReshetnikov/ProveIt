import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeStep
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# Summable relative Taylor errors for the original Barnes logarithm

Subtracting the two quadratic terms introduces the difference
`k*(δ²−η²)/2`, where `δ=h/(Bk)` and `η=h/(Bk+z)`.
Factoring the difference of squares gains a second power of `k`.
The exact finite cubic Mercator residual gains the same power.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeTaylor

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (mul scale normSq normSq_eval normSq_scale series)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalDerivativeRow (offset offset_bound)
open GaussianBarnesCanonicalRelativeStep
  (source numerator denominator radius relative relative_bound reciprocal_margin denominator_positive local_admission)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianGammaEulerHeadLower (translated)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents positive_product canonical_unique
  qadd qmul qmul_canonical qmul_represents represents_rescale represents_congr)
open GaussianRationalMetric (bounded bounded_of_cleared qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (product_difference bounded_sum_same)
open GaussianRationalReciprocal (qone bounded_product bound_congr re_conjugate im_conjugate)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_scale im_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def step (h B k : PTm n) : PTm n := ofGaussian h (B*k)

def quadraticError (z h B k : PTm n) : PTm n :=
  qmul (radiusPoint k two) (qsub (qmul (step h B k) (step h B k)) (qmul (relative z h B k) (relative z h B k)))

def cubicError (z h B k L : PTm n) : PTm n :=
  qmul (radiusPoint k one) (GaussianBarnesCanonicalLogRow.cubic (numerator z h B k) (denominator z B k) L)

@[simp] theorem subst_step {m : ℕ} (σ : Fin n → PTm m) (h B k : PTm n) :
    Syn.subst σ (step h B k) = step (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) := by simp [step]

@[simp] theorem subst_quadraticError {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (quadraticError z h B k) = quadraticError (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [quadraticError,two]

@[simp] theorem subst_cubicError {m : ℕ} (σ : Fin n → PTm m) (z h B k L : PTm n) :
    Syn.subst σ (cubicError z h B k L) =
      cubicError (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ L) := by simp [cubicError,one]

private theorem native_scaled_step (z h B k : PTm n) :
    Γ ⊢[PRAAx] equal (mul (translated z B k) (numerator z h B k)) (scale (denominator z B k) h) := by
  apply equal_of_values <;>
    simp only [numerator,denominator,re_mul,im_mul,re_scale,im_scale,re_conjugate,im_conjugate,normSq_eval] <;> ring

theorem recover_step (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qmul (base z B k) (relative z h B k) ≐ step h B k := by
  let d := B*k
  let E := denominator z B k
  let a := translated z B k
  let u := base z B k
  let v := relative z h B k
  let x := numerator z h B k
  have hk := hs.andE₁.andE₂.andE₁
  have hd := positive_product B k hs.andE₁.andE₁ hk
  have hE := denominator_positive z R B k hs.andE₁
  have raw := qmul_represents u v a x d E hd hE
    (GaussianBarnesCanonicalBase.base_represents z B k hs.andE₁.andE₁ hk) (ofGaussian_represents x E hE)
  exact canonical_unique _ _ (scale E h) (d*E) (qmul_canonical _ _) (ofGaussian_canonical _ _ hd)
    (positive_product _ _ hd hE) (represents_congr (.eqRefl _) (native_scaled_step z h B k) (.eqRefl _) raw)
    (represents_rescale _ _ _ _ (ofGaussian_represents h d hd))

theorem step_difference (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qsub (step h B k) (relative z h B k) ≐ qmul (offset z B k) (relative z h B k) := by
  let w := offset z B k
  let v := relative z h B k
  let d := step h B k
  have hv : Γ ⊢[PRAAx] GaussianRationalHorner.canonical v := ofGaussian_canonical _ _ (denominator_positive z R B k hs.andE₁)
  have a : Γ ⊢[PRAAx] qmul (base z B k) v ≐ qadd v (qmul w v) :=
    (qmul_commutative _ v).eqTrans ((qmul_add v qone w).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (qmul_one_right v hv) (qmul_commutative v w)))
  exact (qsub_congr ((recover_step z h R B k H hs).eqSymm.eqTrans a) (.eqRefl v)).eqTrans
    (qadd_sub_cancel v (qmul w v) (qmul_canonical _ _))

theorem quadratic_bound (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] bounded (quadraticError z h B k) (num 3*R*H*H) ((B*k)*(B*k)) := by
  let d := B*k
  let a := step h B k
  let b := relative z h B k
  let c := qsub a b
  let J := k*d*d
  let U := R*(two*H)
  have hk := hs.andE₁.andE₂.andE₁
  have hd := positive_product B k hs.andE₁.andE₁ hk
  have hkd := positive_product k d hk hd
  have hJ := positive_product _ _ hkd hd
  have h2 : Γ ⊢[PRAAx] le one two := zero_lt_succ one
  have ah : Γ ⊢[PRAAx] bounded a H d :=
    GaussianRationalMetric.bounded_of_same_denominator hd (ofGaussian_represents h d hd) hs.andE₂.andE₂.andE₁
  have bh : Γ ⊢[PRAAx] bounded b (two*H) d := relative_bound z h R B k H hs
  have ch : Γ ⊢[PRAAx] bounded c U (k*d) :=
    bound_congr (step_difference z h R B k H hs).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_product _ _ _ _ _ _ hk hd (offset_bound z R B k hs.andE₁) bh)
  have e₁ := bounded_product c a U (k*d) H d hkd hd ch ah
  have e₂ : Γ ⊢[PRAAx] bounded (qmul b c) ((two*H)*U) J :=
    bound_congr (.eqRefl _) (.eqRefl _) (by dsimp only [J]; ipra_ring) (bounded_product b c (two*H) d U (k*d) hd hkd bh ch)
  have both := bounded_sum_same _ _ _ _ _ hJ e₁ e₂
  have difference : Γ ⊢[PRAAx] bounded (qsub (qmul a a) (qmul b b)) (num 6*R*H*H) J :=
    bound_congr (product_difference a b a b).eqSymm (by dsimp only [U]; ipra_ring) (.eqRefl _) both
  have raw := bounded_product (radiusPoint k two) _ k two _ J h2 hJ (radius_bounded k two h2) difference
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ h2 hJ) (positive_product d d hd hd)
    (le_of_eq_add (d := LeanProofs.ConciseIPRA.PTm.zero) (by simp only [d]; ipra_ring)) raw

private theorem original_cubic_bound (a T E L : PTm n) (hs : Γ ⊢[PRAAx] GaussianLocalLogarithmName.source a T E) :
    Γ ⊢[PRAAx] bounded (GaussianBarnesCanonicalLogRow.cubic a E L) (two*T*T*T) (num 3*E*E*E) := by
  let D := LogarithmRemainder.denominator E L
  let V := series a E L
  let M := num 3*E*E*E
  let A := two*T*T*T
  have hD := LogarithmRemainder.denominator_positive E L hs.andE₁
  have hM := positive_product _ _ (GaussianBarnesCanonicalLogRow.bound_denominator_positive E hs.andE₁) hs.andE₁
  have raw := ComplexLogarithmRemainder.canonical_bound a E T L hs.andE₂.andE₁ hs.andE₂.andE₂
  change Γ ⊢[PRAAx] le (normSq (scale M V)) ((A*D)*(A*D)) at raw
  exact bounded_of_cleared _ _ _ _ _ hD hM (ofGaussian_represents V D hD)
    (le_congr (normSq_scale M V) (by simp only [A,D]; ipra_ring) raw)

theorem finite_cubic_bound (z h R B k H L : PTm n)
    (hs : Γ ⊢[PRAAx] source z h R B k H) (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] bounded (cubicError z h B k L) (num 342*H*H) ((B*k)*(B*k)) := by
  let d := B*k
  let E := denominator z B k
  let T := radius H B k
  let M := num 3*E*E*E
  let X := num 16*H*H
  have hk := hs.andE₁.andE₂.andE₁
  have hd := positive_product B k hs.andE₁.andE₁ hk
  have hE := denominator_positive z R B k hs.andE₁
  have hM := positive_product _ _ (GaussianBarnesCanonicalLogRow.bound_denominator_positive E hE) hE
  have raw := bounded_product (radiusPoint k one) _ k one _ M (le_refl one) hM (radius_bounded k one (le_refl one))
    (original_cubic_bound (numerator z h B k) T E L (local_admission z h R B k H hs))
  have fit : Γ ⊢[PRAAx] le ((k*(two*T*T*T))*(d*d)) ((num 342*H*H)*(one*M)) := by
    have small : Γ ⊢[PRAAx] le (H*k) d := mul_le_mul_right k hH
    have step₁ : Γ ⊢[PRAAx] le ((k*(two*T*T*T))*(d*d)) (X*(d*d)*(d*d)*(d*d)) :=
      le_congr (by dsimp only [X,T,radius,d]; ipra_ring) (by ipra_ring)
        (le_mul_mono (le_refl (X*d*d*d*d*d)) small)
    have margin := reciprocal_margin z R B k hs.andE₁
    have step₂ : Γ ⊢[PRAAx] le (X*(d*d)*(d*d)*(d*d)) (num 1024*H*H*E*E*E) := by
      have e : Γ ⊢[PRAAx] le (d*d) (num 4*E) := margin
      exact le_congr (.eqRefl _) (by dsimp only [X]; ipra_ring)
        (le_mul_mono (le_mul_mono (le_mul_mono (le_refl X) e) e) e)
    exact le_trans step₁ (le_trans step₂ (le_of_eq_add (d := two*H*H*E*E*E) (by dsimp only [M]; ipra_ring)))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (le_refl one) hM) (positive_product d d hd hd) fit raw

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeTaylor
