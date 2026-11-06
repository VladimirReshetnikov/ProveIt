import DiophantineConsistency.Mixed121.W121.TemporalOtherWindows
import DiophantineConsistency.Mixed121.W121.RotationStraddling
import DiophantineConsistency.Mixed121.W121.RotationIndexBounds
/-! Width-121 port of `Compact44/TemporalStraddleWindow` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalStraddleWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem straddling (X n E t r u : V) (hn : 0<n) (hr0 : 0<r) (hr : r<121)
    (he : E%(121*n)=121*t+r) (hL : 121*n=E%(121*n)+((121-r)+u))
    (hi : 121*n-E%(121*n)+121*t=121*(n-1)+(121-r))
    (hX : X<Exp.exp (121*n)) :
    dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      ((dig 121 X 0)*Exp.exp r)%Exp.exp 121 + (dig 121 X (n-1))/Exp.exp (121-r) := by
  have hrr : 121-r<121 := tsub_lt_self (by norm_num) hr0
  have hb : Exp.exp r*Exp.exp (121-r)=Exp.exp 121 := by
    rw [←exp_add,add_tsub_cancel_of_le (le_of_lt hr)]
  have hrev : Exp.exp (121-r)*Exp.exp r=Exp.exp 121 := by rw [mul_comm,hb]
  have hn' : n-1+1=n := tsub_add_cancel_of_le (pos_iff_one_le.mp hn)
  have hnext : dig 121 X ((n-1)+1)=0 := by rw [hn']; exact W121.RotationIndexBounds.last_digit_zero X n hX
  have hsmall : dig 121 X (n-1)/Exp.exp (121-r) < Exp.exp r := by
    apply div_lt_of_lt_mul
    rw [hb]
    exact dig_lt 121 X (n-1)
  have hmodhi := W121.AdjacentDigits.mod_factor (X/Exp.exp (121*n-E%(121*n)+121*t))
    (Exp.exp r) (Exp.exp (121-r)) (exp_pos _)
  rw [hb] at hmodhi
  have hadj := W121.AdjacentDigits.adjacent X (n-1) (121-r) hrr
  rw [hnext,zero_mod,zero_mul,add_zero] at hadj
  have hhigh : (X/Exp.exp (121*n-E%(121*n)+121*t))%Exp.exp r =
      dig 121 X (n-1)/Exp.exp (121-r) := by
    rw [←hmodhi,hi,hadj,mod_eq_self_of_lt hsmall]
  have hmodlo := W121.AdjacentDigits.mod_factor X (Exp.exp (121-r)) (Exp.exp r) (exp_pos _)
  rw [hrev] at hmodlo
  have hlow : (X%Exp.exp (121-r))*Exp.exp r =
      ((dig 121 X 0)*Exp.exp r)%Exp.exp 121 := by
    rw [W121.TemporalWindowFormula.low_piece _ r hr,dig_zero_index,hmodlo]
  rw [W121.RotationStraddling.straddling X (121*n) (E%(121*n)) t r u hr he hL hX,hlow,hhigh]
#print axioms W121.TemporalStraddleWindow.straddling
end W121.TemporalStraddleWindow
