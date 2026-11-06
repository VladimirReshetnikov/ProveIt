import DiophantineConsistency.Mixed121.W121.RotationAdjacent
/-! Width-121 port of `Compact44/RotationWrapped` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.RotationWrapped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wrapped (X L e k u : V) (he : e=121*k+121+u) :
    dig 121 (rot 1 L X e) k = (X / Exp.exp (L-e+121*k)) % Exp.exp 121 := by
  have hp : Exp.exp e = Exp.exp (121*k) * Exp.exp 121 * Exp.exp u := by rw [he, exp_add, exp_add]
  unfold dig rot
  simp only [one_mul]
  rw [hp, add_comm]
  rw [div_mod_add_mul _ _ _ _ _ (exp_pos _) (exp_pos _), ← Arithmetic.div_mul, ← exp_add]

#print axioms W121.RotationWrapped.wrapped
end W121.RotationWrapped
