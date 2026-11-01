import DiophantineConsistency.AdaptiveGap85AllIndicesRoot
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85LargeYPow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Large Y makes the positive signed congruence an equality and excludes
the negative signed congruence, for an arbitrary positive natural E. -/
theorem large_Y_forces_equal (X Y E : V) (hE : 1≤E) (hY : 7*E≤Y)
    (hcong : (27*X)%(4*(Y*(X+1))+3)=(27*E)%(4*(Y*(X+1))+3) ∨
      (27*(1+E*X))%(4*(Y*(X+1))+3)=0) : X=E := by
  let H := 4*(Y*(X+1))+3
  have hp : (7*E)*(X+1)≤Y*(X+1) := mul_le_mul hY (le_refl _) (by simp) (by simp)
  have hH : 28*E*(X+1)+3≤H := by
    dsimp [H]
    have hh := add_le_add (Arithmetic.mul_le_mul_left (a:=(4:V)) hp) (le_refl (3:V))
    calc
      _ = 4*((7*E)*(X+1))+3 := by ring
      _ ≤ _ := hh
  have hEX : X≤E*X := by simpa only [one_mul] using Arithmetic.mul_le_mul_right (a:=X) hE
  have hXsmall : 27*X<H := by
    have hle : 27*X≤27*(E*X) := Arithmetic.mul_le_mul_left hEX
    have hlt : 27*(E*X)<28*E*(X+1)+3 := by
      have hh := lt_add_of_pos_right (27*(E*X)) (show (0:V)<E*X+28*E+3 by simp)
      have he : 27*(E*X)+(E*X+28*E+3)=28*E*(X+1)+3 := by ring
      rwa [he] at hh
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt hH)
  have hEsmall : 27*E<H := by
    have hEpos : 0<E := lt_of_lt_of_le (by simp) hE
    have hlt : 27*E<28*E*(X+1)+3 := by
      have hh := lt_add_of_pos_right (27*E) (show (0:V)<28*E*X+E+3 by simp)
      have he : 27*E+(28*E*X+E+3)=28*E*(X+1)+3 := by ring
      rwa [he] at hh
    exact lt_of_lt_of_le hlt hH
  have hE1 : E-1+1=E := tsub_add_cancel_of_le hE
  have hnegsmall : 27*(1+E*X)<H := by
    have hlt : 27*(1+E*X)<28*E*(X+1)+3 := by
      have hp' : 0<E*X+28*(E-1)+4 := by simp
      have hh := lt_add_of_pos_right (27*(1+E*X)) hp'
      have he : 27*(1+E*X)+(E*X+28*(E-1)+4)=28*E*(X+1)+3 := by
        calc
          _ = 28*E*X+28*(E-1+1)+3 := by ring
          _ = _ := by rw [hE1]; ring
      rwa [he] at hh
    exact lt_of_lt_of_le hlt hH
  rcases hcong with hpos | hneg
  · rw [mod_eq_self_of_lt hXsmall,mod_eq_self_of_lt hEsmall] at hpos
    exact mul_left_cancel₀ (by simp : (27:V)≠0) hpos
  · rw [mod_eq_self_of_lt hnegsmall] at hneg
    have hp' : 0<27*(1+E*X) := mul_pos (by simp) (by simp)
    exact ((ne_of_gt hp') hneg).elim
end DiophantineConsistency.AdaptiveGap85LargeYPow
