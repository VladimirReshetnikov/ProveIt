import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

set_option maxRecDepth 300000 in
set_option maxHeartbeats 80000000 in
theorem rows141To142_product_coefficients :
    ∀ i : Fin 2, ∀ j : Fin 132,
      degreeSevenProductRow ⟨141 + i.1, by omega⟩ j =
        productCoefficient (degreeSevenProductSource ⟨141 + i.1, by omega⟩).2
          (degreeSevenProductSource ⟨141 + i.1, by omega⟩).1
          (degreeSevenRepresentative j) := by
  decide

theorem row141_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨141, by decide⟩ =
      degreeSevenEncodedProduct ⟨141, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  intro j
  simpa using rows141To142_product_coefficients ⟨0, by decide⟩ j

theorem row142_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨142, by decide⟩ =
      degreeSevenEncodedProduct ⟨142, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  intro j
  simpa using rows141To142_product_coefficients ⟨1, by decide⟩ j

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
