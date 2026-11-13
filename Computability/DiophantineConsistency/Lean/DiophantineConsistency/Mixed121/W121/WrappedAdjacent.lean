import DiophantineConsistency.Mixed121.W121.RotationWrapped
/-! Width-121 port of `Compact44/WrappedAdjacent` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.WrappedAdjacent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wrapped_adjacent (X L e k u q r : V)
    (he : e=121*k+121+u) (hi : L-e+121*k=121*q+r) (hr : r<121) :
    dig 121 (rot 1 L X e) k =
      dig 121 X q / Exp.exp r + (dig 121 X (q+1) % Exp.exp r)*Exp.exp (121-r) := by
  rw [W121.RotationWrapped.wrapped X L e k u he, hi]
  exact W121.AdjacentDigits.adjacent X q r hr
#print axioms W121.WrappedAdjacent.wrapped_adjacent
end W121.WrappedAdjacent
