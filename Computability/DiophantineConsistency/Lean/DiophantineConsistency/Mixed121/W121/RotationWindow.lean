import DiophantineConsistency.Mixed121.W121.AdjacentDigits
import DiophantineConsistency.ArithmeticCyclicWord
/-! Width-121 port of `Compact44/RotationWindow` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace W121.RotationWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem unwrapped (X L e k s u : V)
    (hL : L=e+(s+121+u)) (hk : 121*k=e+s) (hX : X<Exp.exp L) :
    dig 121 (rot 1 L X e) k = (X / Exp.exp s) % Exp.exp 121 := by
  have hcut : L-e=s+121+u := by rw [hL, add_tsub_cancel_left]
  have hhigh : X / Exp.exp (L-e) < Exp.exp e := by
    apply div_lt_of_lt_mul
    rw [mul_comm, ← exp_add, tsub_add_cancel_of_le]
    · exact hX
    · rw [hL]; exact le_add_of_nonneg_right (by simp)
  have hexp : Exp.exp (121*k) = Exp.exp e * Exp.exp s := by rw [hk,exp_add]
  unfold dig rot
  simp only [one_mul]
  rw [hexp, Arithmetic.div_mul, div_mul_add _ _ hhigh]
  have hcutexp : Exp.exp (L-e) = Exp.exp s * Exp.exp 121 * Exp.exp u := by
    rw [hcut, exp_add, exp_add]
  have he : X = X % Exp.exp (L-e) + (X / Exp.exp (L-e))* Exp.exp (L-e) := by
    have h := div_add_mod X (Exp.exp (L-e))
    simpa only [add_comm,mul_comm] using h.symm
  have h := div_mod_add_mul (X % Exp.exp (L-e)) (X / Exp.exp (L-e)) (Exp.exp s) (Exp.exp (121:V)) (Exp.exp u) (exp_pos _) (exp_pos _)
  rw [← hcutexp, ← he] at h
  exact h.symm
#print axioms W121.RotationWindow.unwrapped
end W121.RotationWindow
