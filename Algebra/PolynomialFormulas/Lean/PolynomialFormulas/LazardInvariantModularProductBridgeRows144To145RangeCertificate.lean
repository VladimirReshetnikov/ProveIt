import PolynomialFormulas.LazardInvariantModularProductBridgeRows144To145ChunkedCertificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows144To145_literalProduct_eq_encoded :
    ∀ i : Fin 159, 144 ≤ i.1 ∧ i.1 < 146 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 144 ∨ i.1 = 145 := by omega
  rcases hcases with h | h1
  · have hi' : i = ⟨144, by decide⟩ := by ext; exact h
    simpa [hi'] using row144_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨145, by decide⟩ := by ext; exact h1
    simpa [hi'] using row145_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
