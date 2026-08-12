import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row128_product_coefficients_direct :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨128, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨128, by decide⟩).2
          (degreeSevenProductSource ⟨128, by decide⟩).1
          (degreeSevenRepresentative j) := by
  decide

theorem row128_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨128, by decide⟩ =
      degreeSevenEncodedProduct ⟨128, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row128_product_coefficients_direct

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
