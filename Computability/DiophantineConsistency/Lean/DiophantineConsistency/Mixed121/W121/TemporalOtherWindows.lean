import DiophantineConsistency.Mixed121.W121.TemporalWindowFormula
import DiophantineConsistency.Mixed121.W121.WrappedAdjacent
/-! Width-121 port of `Compact44/TemporalOtherWindows` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalOtherWindows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wrapped (X n E t s r u : V) (hr0 : 0<r) (hr : r<121)
    (he : E%(121*n)=121*t+121+u)
    (hi : 121*n-E%(121*n)+121*t=121*s+(121-r)) :
    dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      ((dig 121 X (s+1))*Exp.exp r)%Exp.exp 121 + (dig 121 X s)/Exp.exp (121-r) := by
  have hrr : 121-r<121 := tsub_lt_self (by norm_num) hr0
  have h := W121.WrappedAdjacent.wrapped_adjacent X (121*n) (E%(121*n)) t u s (121-r) he hi hrr
  have hrest : 121-(121-r)=r := tsub_tsub_cancel_of_le (le_of_lt hr)
  rw [hrest] at h
  rw [W121.TemporalWindowFormula.low_piece _ r hr]
  simpa only [add_comm] using h

theorem aligned (X n E t q : V) (ht : t<n) (hq : q<n)
    (he : E%(121*n)=121*q) (hX : X<Exp.exp (121*n)) :
    dig 121 (rot 1 (121*n) X (E%(121*n))) t = dig 121 X (cyc n t q) := by
  rw [he]
  have hrot : rot 1 (121*n) X (121*q)=rot 121 n X q := by
    unfold rot
    simp only [one_mul, ← mul_tsub]
  rw [hrot]
  exact dig_rot 121 n X q t hq ht hX
#print axioms W121.TemporalOtherWindows.wrapped
#print axioms W121.TemporalOtherWindows.aligned
end W121.TemporalOtherWindows
