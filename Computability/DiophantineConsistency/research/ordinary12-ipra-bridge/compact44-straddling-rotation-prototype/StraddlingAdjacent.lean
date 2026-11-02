import DiophantineConsistency.RotationStraddling
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace StraddlingAdjacent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem straddling_adjacent (X L e k a t q r : V)
    (ha : a<67) (he : e=67*k+a) (hL : L=e+((67-a)+t))
    (hX : X<Exp.exp L) (hi : L-e+67*k=67*q+r) (hr : r<67) :
    dig 67 (rot 1 L X e) k =
      (X % Exp.exp (67-a))*Exp.exp a +
      (dig 67 X q / Exp.exp r + (dig 67 X (q+1) % Exp.exp r)*Exp.exp (67-r)) % Exp.exp a := by
  have hb : Exp.exp a * Exp.exp (67-a)=Exp.exp 67 := by
    rw [← exp_add, add_tsub_cancel_of_le (le_of_lt ha)]
  have hm := AdjacentDigits.mod_factor (X / Exp.exp (L-e+67*k))
    (Exp.exp a) (Exp.exp (67-a)) (exp_pos _)
  rw [hb] at hm
  rw [RotationStraddling.straddling X L e k a t ha he hL hX, ← hm, hi,
    AdjacentDigits.adjacent X q r hr]
#print axioms StraddlingAdjacent.straddling_adjacent
end StraddlingAdjacent
