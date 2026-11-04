import DiophantineConsistency.Compact44.TemporalOtherWindows
import DiophantineConsistency.Compact44.RotationStraddling
import DiophantineConsistency.Compact44.RotationIndexBounds
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalStraddleWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem straddling (X n E t r u : V) (hn : 0<n) (hr0 : 0<r) (hr : r<67)
    (he : E%(67*n)=67*t+r) (hL : 67*n=E%(67*n)+((67-r)+u))
    (hi : 67*n-E%(67*n)+67*t=67*(n-1)+(67-r))
    (hX : X<Exp.exp (67*n)) :
    dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      ((dig 67 X 0)*Exp.exp r)%Exp.exp 67 + (dig 67 X (n-1))/Exp.exp (67-r) := by
  have hrr : 67-r<67 := tsub_lt_self (by norm_num) hr0
  have hb : Exp.exp r*Exp.exp (67-r)=Exp.exp 67 := by
    rw [←exp_add,add_tsub_cancel_of_le (le_of_lt hr)]
  have hrev : Exp.exp (67-r)*Exp.exp r=Exp.exp 67 := by rw [mul_comm,hb]
  have hn' : n-1+1=n := tsub_add_cancel_of_le (pos_iff_one_le.mp hn)
  have hnext : dig 67 X ((n-1)+1)=0 := by rw [hn']; exact RotationIndexBounds.last_digit_zero X n hX
  have hsmall : dig 67 X (n-1)/Exp.exp (67-r) < Exp.exp r := by
    apply div_lt_of_lt_mul
    rw [hb]
    exact dig_lt 67 X (n-1)
  have hmodhi := AdjacentDigits.mod_factor (X/Exp.exp (67*n-E%(67*n)+67*t))
    (Exp.exp r) (Exp.exp (67-r)) (exp_pos _)
  rw [hb] at hmodhi
  have hadj := AdjacentDigits.adjacent X (n-1) (67-r) hrr
  rw [hnext,zero_mod,zero_mul,add_zero] at hadj
  have hhigh : (X/Exp.exp (67*n-E%(67*n)+67*t))%Exp.exp r =
      dig 67 X (n-1)/Exp.exp (67-r) := by
    rw [←hmodhi,hi,hadj,mod_eq_self_of_lt hsmall]
  have hmodlo := AdjacentDigits.mod_factor X (Exp.exp (67-r)) (Exp.exp r) (exp_pos _)
  rw [hrev] at hmodlo
  have hlow : (X%Exp.exp (67-r))*Exp.exp r =
      ((dig 67 X 0)*Exp.exp r)%Exp.exp 67 := by
    rw [TemporalWindowFormula.low_piece _ r hr,dig_zero_index,hmodlo]
  rw [RotationStraddling.straddling X (67*n) (E%(67*n)) t r u hr he hL hX,hlow,hhigh]
#print axioms TemporalStraddleWindow.straddling
end TemporalStraddleWindow
