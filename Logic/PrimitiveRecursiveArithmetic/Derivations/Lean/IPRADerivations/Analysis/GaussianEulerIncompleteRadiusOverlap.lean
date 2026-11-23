import IPRADerivations.Analysis.GaussianEulerIncompleteFixedCutoff
import IPRADerivations.Analysis.GaussianEulerIncompleteRadiusAlignment

/-!
# Radius independence of the original incomplete Euler names

Opposite cutoff offsets align the two physical intervals exactly. Both
original cofinal names can query those fixed intervals using their own
tail coefficients. Since auxiliary precision absorbs both coefficients,
the result compares the actual programs at independent requested queries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRadiusOverlap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteName (lowerF upperF data original_regular_names)
open GaussianEulerIncompleteRadiusAlignment (cutoff)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R S B A a b : PTm n) : Fm PTm n :=
  GaussianEulerIncompleteCofinalRate.source z R B A a b ⋏ GaussianEulerIncompleteCofinalRate.source z S B A a b

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R S B A a b : PTm n) :
    (source z R S B A a b).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ S)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [source]

private theorem compare (t x u v y : PTm n) (hl : Γ ⊢[PRAAx] distanceBounded x u (num 3) (unit t))
    (hm : Γ ⊢[PRAAx] distanceBounded u v (unit t+unit t) (unit t*unit t))
    (hr : Γ ⊢[PRAAx] distanceBounded y v (num 3) (unit t)) : Γ ⊢[PRAAx] distanceBounded x y (num 8) (unit t) := by
  have hT := unit_positive (Γ := Γ) t
  have mid := distance_radius_mono _ _ _ _ two (unit t) (positive_product _ _ hT hT) hT
    (le_of_eq_add (d := zero) (by ipra_ring)) hm
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same x u y _ _ _ hT hl
      (distance_triangle_same u v y _ _ _ hT mid (distance_symmetric _ _ _ _ hT hr)))

theorem original_diagonal (t z R S B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R S B A a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 lowerF t (data z R B A a b)) (ap2 lowerF t (data z S B A a b)) (num 8) (unit t) ⋏
    distanceBounded (ap2 upperF t (data z R B A a b)) (ap2 upperF t (data z S B A a b)) (num 8) (unit t) := by
  let m := GaussianEulerIncompleteCutoff.clock t a b
  let k := cutoff m S
  let j := cutoff m R
  have hk : Γ ⊢[PRAAx] le m k := le_add_right _ _
  have hj : Γ ⊢[PRAAx] le m j := le_add_right _ _
  have left := GaussianEulerIncompleteFixedCutoff.original_late_observations t t t k z R B A a b
    (.andI h.andE₁ hk) (le_refl _) (le_refl _)
  have right := GaussianEulerIncompleteFixedCutoff.original_late_observations t t t j z S B A a b
    (.andI h.andE₂ hj) (le_refl _) (le_refl _)
  have hR : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z R B A a b :=
    .andI h.andE₁.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁.andE₁ h.andE₁.andE₂)
  have hS : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z S B A a b :=
    .andI h.andE₂.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₂.andE₁.andE₁.andE₁ h.andE₂.andE₂)
  have mid := GaussianEulerIncompleteRadiusAlignment.original_piece_observations t t t m z R S B A a b hR hS (le_refl _)
  exact .andI (compare t _ _ _ _ left.andE₁ mid.andE₁ right.andE₁)
    (compare t _ _ _ _ left.andE₂ mid.andE₂ right.andE₂)

theorem original_radius_overlap (z R S B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R S B A a b) : Γ ⊢[PRAAx]
    crossEquivalent lowerF lowerF (data z R B A a b) (data z S B A a b) ⋏
    crossEquivalent upperF upperF (data z R B A a b) (data z S B A a b) := by
  let X := data z R B A a b
  let Y := data z S B A a b
  have l := original_regular_names z R B A a b h.andE₁
  have r := original_regular_names z S B A a b h.andE₂
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift S) (Syn.shift B)
      (Syn.shift A) (Syn.shift a) (Syn.shift b) := by simpa only [Fm.shift, Syn.shift, subst_source] using h.shift
  have d := original_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift S) (Syn.shift B)
    (Syn.shift A) (Syn.shift a) (Syn.shift b) hs
  refine .andI (GaussianNameRingLaws.equivalent_of_envelope lowerF lowerF X Y (num 8) l.andE₁ r.andE₁ ?_)
    (GaussianNameRingLaws.equivalent_of_envelope upperF upperF X Y (num 8) l.andE₂ r.andE₂ ?_)
  · refine .allI ?_
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, X, Y, Syn.shift, GaussianEulerIncompleteName.subst_data,
      LeanProofs.IPRA.PTm.subst_num] using d.andE₁
  · refine .allI ?_
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, X, Y, Syn.shift, GaussianEulerIncompleteName.subst_data,
      LeanProofs.IPRA.PTm.subst_num] using d.andE₂

theorem actual_original_incomplete_names_radius_overlap_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        (crossEquivalent lowerF lowerF (data (var 0) (var 1) (var 3) (var 4) (var 5) (var 6))
          (data (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)) ⋏
         crossEquivalent upperF upperF (data (var 0) (var 1) (var 3) (var 4) (var 5) (var 6))
          (data (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)))) :=
  closeUniv 7 (.impI (original_radius_overlap _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRadiusOverlap
