import DiophantineConsistency.Compact44.TemporalCleanNumerics
import DiophantineConsistency.Compact44.RotationAdjacent
import DiophantineConsistency.ArithmeticModularCancellation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalWindowFormula
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem low_piece (x r : V) (hr : r<67) :
    (x*Exp.exp r)%Exp.exp 67 = (x%Exp.exp (67-r))*Exp.exp r := by
  have hb : Exp.exp r * Exp.exp (67-r)=Exp.exp 67 := by
    rw [← exp_add, add_tsub_cancel_of_le (le_of_lt hr)]
  have h := ArithmeticModularCancellation.mul_mod_mul (a:=x) (exp_pos r) (exp_pos (67-r))
  rw [hb] at h
  simpa only [mul_comm] using h

theorem nonwrap (X n E t s r u : V) (hr0 : 0<r) (hr : r<67)
    (hL : 67*n = E%(67*n)+(67*s+(67-r)+67+u))
    (ht : 67*t = E%(67*n)+(67*s+(67-r))) (hX : X<Exp.exp (67*n)) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      ((dig 67 X (s+1))*Exp.exp r)%Exp.exp 67 + (dig 67 X s)/Exp.exp (67-r) := by
  have hrr : 67-r<67 := tsub_lt_self (by norm_num) hr0
  have h := RotationAdjacent.unwrapped_adjacent X (67*n) (E%(67*n)) t s (67-r) u hrr hL ht hX
  have hrest : 67-(67-r)=r := tsub_tsub_cancel_of_le (le_of_lt hr)
  rw [hrest] at h
  rw [low_piece _ r hr]
  simpa only [add_comm] using h
#print axioms TemporalWindowFormula.low_piece
#print axioms TemporalWindowFormula.nonwrap
end TemporalWindowFormula
