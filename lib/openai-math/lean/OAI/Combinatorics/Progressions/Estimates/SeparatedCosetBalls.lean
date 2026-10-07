import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Geometry.RightCosetMetricMap

namespace OAI

section

namespace Erdos3

open scoped ENNReal NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]

theorem dist_le_dist_mul_of_separated_ball (Γ : Subgroup G) (z : G) (R : ℝ)
    (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ))
    {x y : G} (hx : dist x z ≤ R) (hy : dist y z ≤ R) (γ : Γ) :
    dist x y ≤ dist x (y * γ) := by
  by_cases hγ : (γ : G) = 1
  · simp only [hγ, mul_one, le_refl]
  · have hs := hsep γ γ.property hγ
    have hchain : dist z (z * γ) ≤ dist z x + dist x (y * γ) + dist (y * γ) (z * γ) :=
      (dist_triangle z x (z * γ)).trans (by linarith [dist_triangle x (y * γ) (z * γ)])
    rw [dist_mul_right] at hchain
    have hxy := dist_triangle x z y
    rw [dist_comm z x] at hchain
    rw [dist_comm z y] at hxy
    linarith

theorem rightCosetEDist_eq_edist_of_separated_ball (Γ : Subgroup G) (z : G) (R : ℝ)
    (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ))
    {x y : G} (hx : dist x z ≤ R) (hy : dist y z ≤ R) :
    rightCosetEDist Γ x y = edist x y := by
  apply le_antisymm (rightCosetEDist_le Γ x y)
  apply le_iInf
  intro γ
  simp only [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_le_dist_mul_of_separated_ball Γ z R hsep hx hy γ)

omit [IsIsometricSMul Gᵐᵒᵖ G] in
theorem separated_ball_of_lipschitz_left (Γ : Subgroup G) {δ R : ℝ} {C : ℝ≥0}
    (hC : 0 < C) (hgap : ∀ γ ∈ Γ, γ ≠ 1 → δ ≤ dist 1 γ)
    (hR : 4 * R * C ≤ δ) (z : G) (hleft : LipschitzWith C (fun x => z⁻¹ * x)) :
    ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ) := by
  intro γ hγ hne
  have hLip : dist 1 γ ≤ (C : ℝ) * dist z (z * γ) := by
    simpa only [inv_mul_cancel, inv_mul_cancel_left] using hleft.dist_le_mul z (z * γ)
  have hC' : (0 : ℝ) < C := hC
  have hg := hgap γ hγ hne
  nlinarith

variable [IsTopologicalGroup G]

theorem quotient_dist_eq_of_separated_ball (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (z : G) (R : ℝ) (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ)) :
    letI := rightCosetMetricSpace Γ hΓ
    ∀ {x y : G}, dist x z ≤ R → dist y z ≤ R →
      dist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = dist x y := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y hx hy
  have h : edist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = edist x y :=
    rightCosetEDist_eq_edist_of_separated_ball Γ z R hsep hx hy
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using congrArg ENNReal.toReal h

end Erdos3

end

end OAI
