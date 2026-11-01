import DiophantineConsistency.AdaptiveGap85FourthRootCongruence
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FourthLargeY
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The fourth-root congruence forces X=16 once Y is at least 109. -/
theorem fourth_congruence_large_Y (X Y : V) (hY : 109≤Y)
    (hcong : (27*X)%(4*(Y*(X+1))+3)=(27*16)%(4*(Y*(X+1))+3) ∨
      (27*(16*X+1))%(4*(Y*(X+1))+3)=0) : X=16 := by
  let H := 4*(Y*(X+1))+3
  have hp : 109*(X+1)≤Y*(X+1) := mul_le_mul hY (le_refl _) (by simp) (by simp)
  have hH : 436*(X+1)+3≤H := by
    dsimp [H]
    have hh := add_le_add (Arithmetic.mul_le_mul_left (a:=(4:V)) hp) (le_refl (3:V))
    calc
      _ = 4*(109*(X+1))+3 := by ring
      _ ≤ _ := hh
  have hXsmall : 27*X<H := by
    have hh := lt_add_of_pos_right (27*X) (show (0:V)<409*X+439 by simp)
    have he : 27*X+(409*X+439)=436*(X+1)+3 := by ring
    rw [he] at hh
    exact lt_of_lt_of_le hh hH
  have h16small : 27*16<H := by
    have hh := lt_add_of_pos_right (27*16:V) (show (0:V)<436*X+7 by simp)
    have he : 27*16+(436*X+7)=436*(X+1)+3 := by ring
    rw [he] at hh
    exact lt_of_lt_of_le hh hH
  have hnegsmall : 27*(16*X+1)<H := by
    have hh := lt_add_of_pos_right (27*(16*X+1)) (show (0:V)<4*X+412 by simp)
    have he : 27*(16*X+1)+(4*X+412)=436*(X+1)+3 := by ring
    rw [he] at hh
    exact lt_of_lt_of_le hh hH
  rcases hcong with hpos | hneg
  · rw [mod_eq_self_of_lt hXsmall,mod_eq_self_of_lt h16small] at hpos
    exact mul_left_cancel₀ (by simp : (27:V)≠0) hpos
  · rw [mod_eq_self_of_lt hnegsmall] at hneg
    have hp : 0<27*(16*X+1) := mul_pos (by simp) (by simp)
    exact ((ne_of_gt hp) hneg).elim
end DiophantineConsistency.AdaptiveGap85FourthLargeY
