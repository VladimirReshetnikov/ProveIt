import PolynomialFormulas.LazardInvariantModularProductBridgeRows137To138Certificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows137To138_literalProduct_eq_encoded :
    ∀ i : Fin 159, 137 ≤ i.1 ∧ i.1 < 139 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 137 ∨ i.1 = 138 := by omega
  rcases hcases with h | h1
  · have hi' : i = ⟨137, by decide⟩ := by ext; exact h
    simpa [hi'] using row137_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨138, by decide⟩ := by ext; exact h1
    simpa [hi'] using row138_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
