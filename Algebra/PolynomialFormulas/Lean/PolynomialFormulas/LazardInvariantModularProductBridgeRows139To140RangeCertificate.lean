import PolynomialFormulas.LazardInvariantModularProductBridgeRows139To140Certificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows139To140_literalProduct_eq_encoded :
    ∀ i : Fin 159, 139 ≤ i.1 ∧ i.1 < 141 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 139 ∨ i.1 = 140 := by omega
  rcases hcases with h | h1
  · have hi' : i = ⟨139, by decide⟩ := by ext; exact h
    simpa [hi'] using row139_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨140, by decide⟩ := by ext; exact h1
    simpa [hi'] using row140_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
