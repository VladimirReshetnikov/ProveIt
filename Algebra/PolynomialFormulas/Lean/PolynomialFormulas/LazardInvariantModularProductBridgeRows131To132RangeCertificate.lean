import PolynomialFormulas.LazardInvariantModularProductBridgeRows131To132Certificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows131To132_literalProduct_eq_encoded :
    ∀ i : Fin 159, 131 ≤ i.1 ∧ i.1 < 133 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 131 ∨ i.1 = 132 := by omega
  rcases hcases with h | h1
  · have hi' : i = ⟨131, by decide⟩ := by ext; exact h
    simpa [hi'] using row131_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨132, by decide⟩ := by ext; exact h1
    simpa [hi'] using row132_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
