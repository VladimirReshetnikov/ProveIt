import PolynomialFormulas.LazardInvariantModularProductBridgeRow120Certificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRow121Certificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRow122Certificate
import PolynomialFormulas.LazardInvariantModularProductBridgeRow123Certificate

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

theorem rows120To123_literalProduct_eq_encoded :
    ∀ i : Fin 159, 120 ≤ i.1 ∧ i.1 < 124 →
      degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  intro i hi
  have hcases : i.1 = 120 ∨ i.1 = 121 ∨ i.1 = 122 ∨ i.1 = 123 := by omega
  rcases hcases with h | h1 | h2 | h3
  · have hi' : i = ⟨120, by decide⟩ := by ext; exact h
    simpa [hi'] using row120_literalProduct_eq_encoded
  · have hi' : i = ⟨121, by decide⟩ := by ext; exact h1
    simpa [hi'] using row121_literalProduct_eq_encoded
  · have hi' : i = ⟨122, by decide⟩ := by ext; exact h2
    simpa [hi'] using row122_literalProduct_eq_encoded
  · have hi' : i = ⟨123, by decide⟩ := by ext; exact h3
    simpa [hi'] using row123_literalProduct_eq_encoded

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
