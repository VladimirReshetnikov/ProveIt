import PolynomialFormulas.LazardInvariantModularProductBridgeRows135To136Certificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows135To136_literalProduct_eq_encoded :
    ∀ i : Fin 159, 135 ≤ i.1 ∧ i.1 < 137 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 135 ∨ i.1 = 136 := by omega
  rcases hcases with h | h1
  · have hi' : i = ⟨135, by decide⟩ := by ext; exact h
    simpa [hi'] using row135_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨136, by decide⟩ := by ext; exact h1
    simpa [hi'] using row136_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
