import DiophantineConsistency.AdaptiveGap85BalanceModel

/-! A strictly decreasing gap when the balance shift is actually available. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85BalanceProgress
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85BalanceModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gap_strictly_decreases (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V)
    (hb : 0<v 0*(p 0:V)) (ht : 0<t)
    (hC : let b := v 0*(p 0:V); let q := 1+b; q*b*t≤v 2) :
    shift p v t 1+shift p v t 2 < v 1+v 2 := by
  have he := shifted_gap_sum p v t hC
  have hd : 0<(v 0*(p 0:V))*(v 0*(p 0:V))*t := mul_pos (mul_pos hb hb) ht
  rw [←he]
  exact lt_add_of_pos_right _ hd
end DiophantineConsistency.AdaptiveGap85BalanceProgress
