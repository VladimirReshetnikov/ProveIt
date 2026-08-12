import PolynomialFormulas.LazardInvariantModularProductBridgeRows129To130Certificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows129To130_literalProduct_eq_encoded :
    ∀ i : Fin 159, 129 ≤ i.1 ∧ i.1 < 131 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 129 ∨ i.1 = 130 := by omega
  rcases hcases with h | h1
  · have hi' : i = ⟨129, by decide⟩ := by ext; exact h
    simpa [hi'] using row129_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨130, by decide⟩ := by ext; exact h1
    simpa [hi'] using row130_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
