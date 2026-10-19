import GowersSzemeredi.Proofs18ExponentialProduct
import GowersSzemeredi.Proofs16ClassStep

/-! Facts shared by the class steps of route (II) (Notes L.6, E5 part B): the
vertex count `classVertexNum_succ_le`, the scale bound `inv_scale_le` and the
monotonicity `uniformBase_mono_V` of the uniform base.

The step with explicit degrees (`powerUniformClass_succ`) is in
`Proofs16ClassStepDegreesSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Shared facts -/

theorem classVertexNum_succ_le (k : Nat) : classVertexNum k + 1 ≤ 2 ^ k := by
  unfold classVertexNum
  have h : (otherVertices k).card ≤ 2 ^ k := by
    unfold otherVertices
    refine (Finset.card_filter_le _ _).trans ?_
    simp [Finset.card_univ]
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

theorem inv_scale_le {w rho : Real} {c : Real} {j : Nat} (hw : 2 ≤ w) (hr : 0 < rho)
    (hrw : rho⁻¹ ≤ w) (hc : c ≤ 2 ^ j) : (rho / c)⁻¹ ≤ w ^ (j + 1) := by
  rw [inv_div, div_eq_mul_inv, pow_succ]
  exact mul_le_mul (const_le_pow hw hc) hrw (inv_pos.mpr hr).le (pow_nonneg (by linarith) _)

/-! ### Weakening a class -/

theorem uniformBase_mono_V {V V' : Real} (hVV : V ≤ V') (n : Nat) {theta gamma rho : Real}
    (ht : 0 < theta) (hg : 0 < gamma) (hr : 0 ≤ rho) :
    uniformBase V n theta gamma rho ≤ uniformBase V' n theta gamma rho := by
  unfold uniformBase
  have h0 : 0 ≤ 2 / (gamma * theta * rho) := div_nonneg (by norm_num) (by positivity)
  have hn : (0 : Real) ≤ (n : Real) + 1 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVV hn) h0

end LeanProofs.GowersSzemeredi
