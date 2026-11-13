import DiophantineConsistency.RotationAdjacent
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RotationWrapped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wrapped (X L e k u : V) (he : e=67*k+67+u) :
    dig 67 (rot 1 L X e) k = (X / Exp.exp (L-e+67*k)) % Exp.exp 67 := by
  have hp : Exp.exp e = Exp.exp (67*k) * Exp.exp 67 * Exp.exp u := by rw [he, exp_add, exp_add]
  unfold dig rot
  simp only [one_mul]
  rw [hp, add_comm]
  rw [div_mod_add_mul _ _ _ _ _ (exp_pos _) (exp_pos _), ← Arithmetic.div_mul, ← exp_add]

#print axioms RotationWrapped.wrapped
end RotationWrapped
