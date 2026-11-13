import DiophantineConsistency.TemporalWindowFormula
import DiophantineConsistency.WrappedAdjacent
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalOtherWindows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wrapped (X n E t s r u : V) (hr0 : 0<r) (hr : r<67)
    (he : E%(67*n)=67*t+67+u)
    (hi : 67*n-E%(67*n)+67*t=67*s+(67-r)) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      ((dig 67 X (s+1))*Exp.exp r)%Exp.exp 67 + (dig 67 X s)/Exp.exp (67-r) := by
  have hrr : 67-r<67 := tsub_lt_self (by norm_num) hr0
  have h := WrappedAdjacent.wrapped_adjacent X (67*n) (E%(67*n)) t u s (67-r) he hi hrr
  have hrest : 67-(67-r)=r := tsub_tsub_cancel_of_le (le_of_lt hr)
  rw [hrest] at h
  rw [TemporalWindowFormula.low_piece _ r hr]
  simpa only [add_comm] using h

theorem aligned (X n E t q : V) (ht : t<n) (hq : q<n)
    (he : E%(67*n)=67*q) (hX : X<Exp.exp (67*n)) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t = dig 67 X (cyc n t q) := by
  rw [he]
  have hrot : rot 1 (67*n) X (67*q)=rot 67 n X q := by
    unfold rot
    simp only [one_mul, ← mul_tsub]
  rw [hrot]
  exact dig_rot 67 n X q t hq ht hX
#print axioms TemporalOtherWindows.wrapped
#print axioms TemporalOtherWindows.aligned
end TemporalOtherWindows
