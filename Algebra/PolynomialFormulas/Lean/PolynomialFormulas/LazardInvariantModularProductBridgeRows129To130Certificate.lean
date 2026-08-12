import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

set_option maxRecDepth 300000 in
set_option maxHeartbeats 80000000 in
theorem rows129To130_product_coefficients :
    ∀ i : Fin 2, ∀ j : Fin 132,
      degreeSevenProductRow ⟨129 + i.1, by omega⟩ j =
        productCoefficient (degreeSevenProductSource ⟨129 + i.1, by omega⟩).2
          (degreeSevenProductSource ⟨129 + i.1, by omega⟩).1
          (degreeSevenRepresentative j) := by
  decide

theorem row129_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨129, by decide⟩ =
      degreeSevenEncodedProduct ⟨129, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  intro j
  simpa using rows129To130_product_coefficients ⟨0, by decide⟩ j

theorem row130_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨130, by decide⟩ =
      degreeSevenEncodedProduct ⟨130, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  intro j
  simpa using rows129To130_product_coefficients ⟨1, by decide⟩ j

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
