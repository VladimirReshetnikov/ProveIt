import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

set_option maxRecDepth 300000 in
set_option maxHeartbeats 80000000 in
theorem rows139To140_product_coefficients :
    ∀ i : Fin 2, ∀ j : Fin 132,
      degreeSevenProductRow ⟨139 + i.1, by omega⟩ j =
        productCoefficient (degreeSevenProductSource ⟨139 + i.1, by omega⟩).2
          (degreeSevenProductSource ⟨139 + i.1, by omega⟩).1
          (degreeSevenRepresentative j) := by
  decide

theorem row139_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨139, by decide⟩ =
      degreeSevenEncodedProduct ⟨139, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  intro j
  simpa using rows139To140_product_coefficients ⟨0, by decide⟩ j

theorem row140_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨140, by decide⟩ =
      degreeSevenEncodedProduct ⟨140, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  intro j
  simpa using rows139To140_product_coefficients ⟨1, by decide⟩ j

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
