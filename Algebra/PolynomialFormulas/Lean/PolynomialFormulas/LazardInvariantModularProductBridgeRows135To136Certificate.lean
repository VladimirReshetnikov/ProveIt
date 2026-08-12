import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

set_option maxRecDepth 300000 in
set_option maxHeartbeats 80000000 in
theorem rows135To136_product_coefficients :
    ∀ i : Fin 2, ∀ j : Fin 132,
      degreeSevenProductRow ⟨135 + i.1, by omega⟩ j =
        productCoefficient (degreeSevenProductSource ⟨135 + i.1, by omega⟩).2
          (degreeSevenProductSource ⟨135 + i.1, by omega⟩).1
          (degreeSevenRepresentative j) := by
  decide

theorem row135_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨135, by decide⟩ =
      degreeSevenEncodedProduct ⟨135, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  intro j
  simpa using rows135To136_product_coefficients ⟨0, by decide⟩ j

theorem row136_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨136, by decide⟩ =
      degreeSevenEncodedProduct ⟨136, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  intro j
  simpa using rows135To136_product_coefficients ⟨1, by decide⟩ j

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
