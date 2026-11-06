import DiophantineConsistency.Mixed121.W121.RotationWindow
/-! Width-121 port of `Compact44/RotationAdjacent` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.RotationAdjacent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem unwrapped_adjacent (X L e k q r u : V)
    (hr : r<121) (hL : L=e+(121*q+r+121+u))
    (hk : 121*k=e+(121*q+r)) (hX : X<Exp.exp L) :
    dig 121 (rot 1 L X e) k =
      dig 121 X q / Exp.exp r +
      (dig 121 X (q+1) % Exp.exp r) * Exp.exp (121-r) := by
  rw [W121.RotationWindow.unwrapped X L e k (121*q+r) u hL hk hX]
  exact W121.AdjacentDigits.adjacent X q r hr
#print axioms W121.RotationAdjacent.unwrapped_adjacent
end W121.RotationAdjacent
