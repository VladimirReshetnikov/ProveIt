import DiophantineConsistency.RotationWindow
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RotationAdjacent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem unwrapped_adjacent (X L e k q r u : V)
    (hr : r<67) (hL : L=e+(67*q+r+67+u))
    (hk : 67*k=e+(67*q+r)) (hX : X<Exp.exp L) :
    dig 67 (rot 1 L X e) k =
      dig 67 X q / Exp.exp r +
      (dig 67 X (q+1) % Exp.exp r) * Exp.exp (67-r) := by
  rw [RotationWindow.unwrapped X L e k (67*q+r) u hL hk hX]
  exact AdjacentDigits.adjacent X q r hr
#print axioms RotationAdjacent.unwrapped_adjacent
end RotationAdjacent
