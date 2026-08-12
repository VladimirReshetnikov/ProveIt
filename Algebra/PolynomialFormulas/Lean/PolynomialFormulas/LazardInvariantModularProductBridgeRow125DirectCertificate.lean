import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row125_product_coefficients_direct :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨125, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨125, by decide⟩).2
          (degreeSevenProductSource ⟨125, by decide⟩).1
          (degreeSevenRepresentative j) := by
  decide

theorem row125_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨125, by decide⟩ =
      degreeSevenEncodedProduct ⟨125, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row125_product_coefficients_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
