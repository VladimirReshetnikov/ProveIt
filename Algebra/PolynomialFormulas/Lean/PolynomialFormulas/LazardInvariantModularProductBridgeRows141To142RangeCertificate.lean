import PolynomialFormulas.LazardInvariantModularProductBridgeRows141To142Certificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows141To142_literalProduct_eq_encoded :
    ∀ i : Fin 159, 141 ≤ i.1 ∧ i.1 < 143 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 141 ∨ i.1 = 142 := by omega
  rcases hcases with h | h1
  · have hi' : i = ⟨141, by decide⟩ := by ext; exact h
    simpa [hi'] using row141_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨142, by decide⟩ := by ext; exact h1
    simpa [hi'] using row142_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
