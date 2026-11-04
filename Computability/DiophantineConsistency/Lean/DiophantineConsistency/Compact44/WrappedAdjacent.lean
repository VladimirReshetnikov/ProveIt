import DiophantineConsistency.Compact44.RotationWrapped
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace WrappedAdjacent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wrapped_adjacent (X L e k u q r : V)
    (he : e=67*k+67+u) (hi : L-e+67*k=67*q+r) (hr : r<67) :
    dig 67 (rot 1 L X e) k =
      dig 67 X q / Exp.exp r + (dig 67 X (q+1) % Exp.exp r)*Exp.exp (67-r) := by
  rw [RotationWrapped.wrapped X L e k u he, hi]
  exact AdjacentDigits.adjacent X q r hr
#print axioms WrappedAdjacent.wrapped_adjacent
end WrappedAdjacent
