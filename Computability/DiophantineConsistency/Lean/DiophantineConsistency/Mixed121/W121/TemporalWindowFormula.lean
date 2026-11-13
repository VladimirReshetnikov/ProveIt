import DiophantineConsistency.Mixed121.W121.TemporalCleanNumerics
import DiophantineConsistency.Mixed121.W121.RotationAdjacent
import DiophantineConsistency.ArithmeticModularCancellation
/-! Width-121 port of `Compact44/TemporalWindowFormula` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalWindowFormula
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem low_piece (x r : V) (hr : r<121) :
    (x*Exp.exp r)%Exp.exp 121 = (x%Exp.exp (121-r))*Exp.exp r := by
  have hb : Exp.exp r * Exp.exp (121-r)=Exp.exp 121 := by
    rw [← exp_add, add_tsub_cancel_of_le (le_of_lt hr)]
  have h := ArithmeticModularCancellation.mul_mod_mul (a:=x) (exp_pos r) (exp_pos (121-r))
  rw [hb] at h
  simpa only [mul_comm] using h

theorem nonwrap (X n E t s r u : V) (hr0 : 0<r) (hr : r<121)
    (hL : 121*n = E%(121*n)+(121*s+(121-r)+121+u))
    (ht : 121*t = E%(121*n)+(121*s+(121-r))) (hX : X<Exp.exp (121*n)) :
    dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      ((dig 121 X (s+1))*Exp.exp r)%Exp.exp 121 + (dig 121 X s)/Exp.exp (121-r) := by
  have hrr : 121-r<121 := tsub_lt_self (by norm_num) hr0
  have h := W121.RotationAdjacent.unwrapped_adjacent X (121*n) (E%(121*n)) t s (121-r) u hrr hL ht hX
  have hrest : 121-(121-r)=r := tsub_tsub_cancel_of_le (le_of_lt hr)
  rw [hrest] at h
  rw [low_piece _ r hr]
  simpa only [add_comm] using h
#print axioms W121.TemporalWindowFormula.low_piece
#print axioms W121.TemporalWindowFormula.nonwrap
end W121.TemporalWindowFormula
