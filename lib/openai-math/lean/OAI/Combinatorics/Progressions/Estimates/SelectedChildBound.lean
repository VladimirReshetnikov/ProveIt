/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FiniteCellRefinement

namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem active_center_integral_le
    (Z : Finset (G × G)) (L S : Finset G) (a f g : G → ℝ) (origin : G)
    (shape : G × G → Finset G) (active : G × G → Bool) {T : ℝ}
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (hchild : ∀ z ∈ Z, active z = true → CellBilinearBound (shape z) a T) :
    (𝔼 z ∈ Z, if active z = true then
      centerChildIntegral L S (fun r => a (origin + r)) f g z (shape z) else 0) ≤
      T * (𝔼 z ∈ Z, if active z = true then centerChildPotential L S f g z (shape z) else 0) := by
  calc
    _ ≤ 𝔼 z ∈ Z, T * (if active z = true then centerChildPotential L S f g z (shape z) else 0) := by
      apply Finset.expect_le_expect
      intro z hz
      by_cases ha : active z = true
      · simpa only [ite_eq_left ha] using
          centerChildIntegral_le_of_cellBilinearBound L S (shape z) a f g origin z (hchild z hz ha) hf hg
      · simp only [ite_eq_right ha, mul_zero, le_refl]
    _ = _ := (Finset.mul_expect _ _ T).symm

theorem parent_bound_of_selected_children
    (Z : Finset (G × G)) (L S : Finset G) (a f g : G → ℝ) (origin : G)
    (shape : G × G → Finset G) (active : G × G → Bool)
    {parent T rho Phi error : ℝ} (hT : 0 ≤ T)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (hchild : ∀ z ∈ Z, active z = true → CellBilinearBound (shape z) a T)
    (hpotential : (𝔼 z ∈ Z, if active z = true then centerChildPotential L S f g z (shape z) else 0) ≤
      rho * Phi)
    (hparent : parent ≤ (𝔼 z ∈ Z, if active z = true then
      centerChildIntegral L S (fun r => a (origin + r)) f g z (shape z) else 0) + error) :
    parent ≤ T * rho * Phi + error := by
  have hsum := active_center_integral_le Z L S a f g origin shape active hf hg hchild
  calc
    _ ≤ T * (𝔼 z ∈ Z, if active z = true then centerChildPotential L S f g z (shape z) else 0) + error :=
      hparent.trans (add_le_add hsum le_rfl)
    _ ≤ T * (rho * Phi) + error := add_le_add (mul_le_mul_of_nonneg_left hpotential hT) le_rfl
    _ = _ := by rw [mul_assoc]

end Erdos3.CellRefinement

end

end OAI
