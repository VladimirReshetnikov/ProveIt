import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

def row121ProductMonomials : List Exponent := [
  ![1, 1, 1, 1, 2, 1],
  ![1, 1, 1, 2, 1, 1],
  ![1, 1, 1, 2, 2, 0],
  ![1, 1, 2, 1, 1, 1],
  ![1, 1, 2, 1, 2, 0],
  ![1, 1, 2, 2, 1, 0],
  ![1, 2, 1, 1, 1, 1],
  ![1, 2, 1, 1, 2, 0],
  ![1, 2, 1, 2, 1, 0],
  ![1, 2, 2, 1, 1, 0],
  ![2, 1, 1, 1, 1, 1],
  ![2, 1, 1, 1, 2, 0],
  ![2, 1, 1, 2, 1, 0],
  ![2, 1, 2, 1, 1, 0],
  ![2, 2, 1, 1, 1, 0],
  ![1, 1, 1, 1, 1, 2],
  ![1, 1, 1, 2, 0, 2],
  ![1, 1, 1, 2, 1, 1],
  ![1, 1, 2, 1, 0, 2],
  ![1, 1, 2, 1, 1, 1],
  ![1, 1, 2, 2, 0, 1],
  ![1, 2, 1, 1, 0, 2],
  ![1, 2, 1, 1, 1, 1],
  ![1, 2, 1, 2, 0, 1],
  ![1, 2, 2, 1, 0, 1],
  ![2, 1, 1, 1, 0, 2],
  ![2, 1, 1, 1, 1, 1],
  ![2, 1, 1, 2, 0, 1],
  ![2, 1, 2, 1, 0, 1],
  ![2, 2, 1, 1, 0, 1],
  ![1, 1, 1, 0, 2, 2],
  ![1, 1, 1, 1, 1, 2],
  ![1, 1, 1, 1, 2, 1],
  ![1, 1, 2, 0, 1, 2],
  ![1, 1, 2, 0, 2, 1],
  ![1, 1, 2, 1, 1, 1],
  ![1, 2, 1, 0, 1, 2],
  ![1, 2, 1, 0, 2, 1],
  ![1, 2, 1, 1, 1, 1],
  ![1, 2, 2, 0, 1, 1],
  ![2, 1, 1, 0, 1, 2],
  ![2, 1, 1, 0, 2, 1],
  ![2, 1, 1, 1, 1, 1],
  ![2, 1, 2, 0, 1, 1],
  ![2, 2, 1, 0, 1, 1],
  ![1, 1, 0, 1, 2, 2],
  ![1, 1, 0, 2, 1, 2],
  ![1, 1, 0, 2, 2, 1],
  ![1, 1, 1, 1, 1, 2],
  ![1, 1, 1, 1, 2, 1],
  ![1, 1, 1, 2, 1, 1],
  ![1, 2, 0, 1, 1, 2],
  ![1, 2, 0, 1, 2, 1],
  ![1, 2, 0, 2, 1, 1],
  ![1, 2, 1, 1, 1, 1],
  ![2, 1, 0, 1, 1, 2],
  ![2, 1, 0, 1, 2, 1],
  ![2, 1, 0, 2, 1, 1],
  ![2, 1, 1, 1, 1, 1],
  ![2, 2, 0, 1, 1, 1],
  ![1, 0, 1, 1, 2, 2],
  ![1, 0, 1, 2, 1, 2],
  ![1, 0, 1, 2, 2, 1],
  ![1, 0, 2, 1, 1, 2],
  ![1, 0, 2, 1, 2, 1],
  ![1, 0, 2, 2, 1, 1],
  ![1, 1, 1, 1, 1, 2],
  ![1, 1, 1, 1, 2, 1],
  ![1, 1, 1, 2, 1, 1],
  ![1, 1, 2, 1, 1, 1],
  ![2, 0, 1, 1, 1, 2],
  ![2, 0, 1, 1, 2, 1],
  ![2, 0, 1, 2, 1, 1],
  ![2, 0, 2, 1, 1, 1],
  ![2, 1, 1, 1, 1, 1],
  ![0, 1, 1, 1, 2, 2],
  ![0, 1, 1, 2, 1, 2],
  ![0, 1, 1, 2, 2, 1],
  ![0, 1, 2, 1, 1, 2],
  ![0, 1, 2, 1, 2, 1],
  ![0, 1, 2, 2, 1, 1],
  ![0, 2, 1, 1, 1, 2],
  ![0, 2, 1, 1, 2, 1],
  ![0, 2, 1, 2, 1, 1],
  ![0, 2, 2, 1, 1, 1],
  ![1, 1, 1, 1, 1, 2],
  ![1, 1, 1, 1, 2, 1],
  ![1, 1, 1, 2, 1, 1],
  ![1, 1, 2, 1, 1, 1],
  ![1, 2, 1, 1, 1, 1]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row121ProductMonomials_eq :
    productMonomials (degreeSevenProductSource ⟨121, by decide⟩).2
      (degreeSevenProductSource ⟨121, by decide⟩).1 =
      row121ProductMonomials := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row121_product_coefficients :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨121, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨121, by decide⟩).2
          (degreeSevenProductSource ⟨121, by decide⟩).1
          (degreeSevenRepresentative j) := by
  unfold productCoefficient
  rw [row121ProductMonomials_eq]
  decide

theorem row121_literalProduct_eq_encoded :
    degreeSevenLiteralProduct ⟨121, by decide⟩ =
      degreeSevenEncodedProduct ⟨121, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row121_product_coefficients

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
