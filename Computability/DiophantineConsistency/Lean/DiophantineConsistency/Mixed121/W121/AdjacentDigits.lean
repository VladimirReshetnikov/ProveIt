import DiophantineConsistency.Compact44.FractionalDigits
/-! Width-121 port of `Compact44/AdjacentDigits` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.AdjacentDigits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mod_factor (Z d t : V) (hd : 0<d) : (Z % (d*t)) % d = Z % d := by
  have he := div_add_mod Z (d*t)
  conv_rhs => rw [← he]
  rw [show d*t*(Z/(d*t))+Z%(d*t) = Z%(d*t)+(t*(Z/(d*t)))*d by ring,
    mod_add_mul _ _ hd]

theorem adjacent (X q r : V) (hr : r<121) :
    (X / Exp.exp (121*q+r)) % Exp.exp 121 =
      dig 121 X q / Exp.exp r +
      (dig 121 X (q+1) % Exp.exp r) * Exp.exp (121-r) := by
  have hb : Exp.exp r * Exp.exp (121-r) = Exp.exp 121 := by
    rw [← exp_add, add_tsub_cancel_of_le (le_of_lt hr)]
  have h := FractionalDigits.split_quotient (X/Exp.exp (121*q))
    (Exp.exp r) (Exp.exp (121-r)) (exp_pos _) (exp_pos _)
  rw [hb] at h
  have hm := mod_factor (X / Exp.exp (121*q) / Exp.exp 121) (Exp.exp r) (Exp.exp (121-r)) (exp_pos _)
  rw [hb] at hm
  rw [← hm] at h
  simpa only [dig, div_exp_succ, ← Arithmetic.div_mul, ← exp_add] using h
#print axioms W121.AdjacentDigits.mod_factor
#print axioms W121.AdjacentDigits.adjacent
end W121.AdjacentDigits
