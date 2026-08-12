import PolynomialFormulas.LazardInvariantModularProductBridgeRow124DirectCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRow125DirectCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRow126DirectCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRow127DirectCertificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRow128DirectCertificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows124To128_literalProduct_eq_encoded :
    ∀ i : Fin 159, 124 ≤ i.1 ∧ i.1 < 129 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 124 ∨ i.1 = 125 ∨ i.1 = 126 ∨ i.1 = 127 ∨ i.1 = 128 := by omega
  rcases hcases with h | h1 | h2 | h3 | h4
  · have hi' : i = ⟨124, by decide⟩ := by ext; exact h
    simpa [hi'] using row124_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨125, by decide⟩ := by ext; exact h1
    simpa [hi'] using row125_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨126, by decide⟩ := by ext; exact h2
    simpa [hi'] using row126_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨127, by decide⟩ := by ext; exact h3
    simpa [hi'] using row127_literalProduct_eq_encoded_direct
  · have hi' : i = ⟨128, by decide⟩ := by ext; exact h4
    simpa [hi'] using row128_literalProduct_eq_encoded_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
