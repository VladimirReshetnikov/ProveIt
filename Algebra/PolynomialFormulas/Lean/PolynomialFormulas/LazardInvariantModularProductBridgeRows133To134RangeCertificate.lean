import PolynomialFormulas.LazardInvariantModularProductBridgeRows133To134Certificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows133To134_literalProduct_eq_encoded :
    ∀ i : Fin 159, 133 ≤ i.1 ∧ i.1 < 135 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 133 ∨ i.1 = 134 := by omega
  rcases hcases with h | h1
  · have hi' : i = ⟨133, by decide⟩ := by ext; exact h
    simpa [hi'] using row133_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨134, by decide⟩ := by ext; exact h1
    simpa [hi'] using row134_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
