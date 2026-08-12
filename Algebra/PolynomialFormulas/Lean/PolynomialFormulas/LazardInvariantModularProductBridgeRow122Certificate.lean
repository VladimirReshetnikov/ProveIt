import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

def row122ProductMonomials : List Exponent := [
  ![4, 0, 0, 1, 1, 1],
  ![4, 0, 1, 0, 1, 1],
  ![4, 0, 1, 1, 0, 1],
  ![4, 0, 1, 1, 1, 0],
  ![4, 1, 0, 0, 1, 1],
  ![4, 1, 0, 1, 0, 1],
  ![4, 1, 0, 1, 1, 0],
  ![4, 1, 1, 0, 0, 1],
  ![4, 1, 1, 0, 1, 0],
  ![4, 1, 1, 1, 0, 0],
  ![5, 0, 0, 0, 1, 1],
  ![5, 0, 0, 1, 0, 1],
  ![5, 0, 0, 1, 1, 0],
  ![5, 0, 1, 0, 0, 1],
  ![5, 0, 1, 0, 1, 0],
  ![5, 0, 1, 1, 0, 0],
  ![5, 1, 0, 0, 0, 1],
  ![5, 1, 0, 0, 1, 0],
  ![5, 1, 0, 1, 0, 0],
  ![5, 1, 1, 0, 0, 0],
  ![0, 0, 0, 1, 1, 5],
  ![0, 0, 1, 0, 1, 5],
  ![0, 0, 1, 1, 0, 5],
  ![0, 0, 1, 1, 1, 4],
  ![0, 1, 0, 0, 1, 5],
  ![0, 1, 0, 1, 0, 5],
  ![0, 1, 0, 1, 1, 4],
  ![0, 1, 1, 0, 0, 5],
  ![0, 1, 1, 0, 1, 4],
  ![0, 1, 1, 1, 0, 4],
  ![1, 0, 0, 0, 1, 5],
  ![1, 0, 0, 1, 0, 5],
  ![1, 0, 0, 1, 1, 4],
  ![1, 0, 1, 0, 0, 5],
  ![1, 0, 1, 0, 1, 4],
  ![1, 0, 1, 1, 0, 4],
  ![1, 1, 0, 0, 0, 5],
  ![1, 1, 0, 0, 1, 4],
  ![1, 1, 0, 1, 0, 4],
  ![1, 1, 1, 0, 0, 4],
  ![0, 0, 0, 1, 5, 1],
  ![0, 0, 1, 0, 5, 1],
  ![0, 0, 1, 1, 4, 1],
  ![0, 0, 1, 1, 5, 0],
  ![0, 1, 0, 0, 5, 1],
  ![0, 1, 0, 1, 4, 1],
  ![0, 1, 0, 1, 5, 0],
  ![0, 1, 1, 0, 4, 1],
  ![0, 1, 1, 0, 5, 0],
  ![0, 1, 1, 1, 4, 0],
  ![1, 0, 0, 0, 5, 1],
  ![1, 0, 0, 1, 4, 1],
  ![1, 0, 0, 1, 5, 0],
  ![1, 0, 1, 0, 4, 1],
  ![1, 0, 1, 0, 5, 0],
  ![1, 0, 1, 1, 4, 0],
  ![1, 1, 0, 0, 4, 1],
  ![1, 1, 0, 0, 5, 0],
  ![1, 1, 0, 1, 4, 0],
  ![1, 1, 1, 0, 4, 0],
  ![0, 0, 0, 5, 1, 1],
  ![0, 0, 1, 4, 1, 1],
  ![0, 0, 1, 5, 0, 1],
  ![0, 0, 1, 5, 1, 0],
  ![0, 1, 0, 4, 1, 1],
  ![0, 1, 0, 5, 0, 1],
  ![0, 1, 0, 5, 1, 0],
  ![0, 1, 1, 4, 0, 1],
  ![0, 1, 1, 4, 1, 0],
  ![0, 1, 1, 5, 0, 0],
  ![1, 0, 0, 4, 1, 1],
  ![1, 0, 0, 5, 0, 1],
  ![1, 0, 0, 5, 1, 0],
  ![1, 0, 1, 4, 0, 1],
  ![1, 0, 1, 4, 1, 0],
  ![1, 0, 1, 5, 0, 0],
  ![1, 1, 0, 4, 0, 1],
  ![1, 1, 0, 4, 1, 0],
  ![1, 1, 0, 5, 0, 0],
  ![1, 1, 1, 4, 0, 0],
  ![0, 0, 4, 1, 1, 1],
  ![0, 0, 5, 0, 1, 1],
  ![0, 0, 5, 1, 0, 1],
  ![0, 0, 5, 1, 1, 0],
  ![0, 1, 4, 0, 1, 1],
  ![0, 1, 4, 1, 0, 1],
  ![0, 1, 4, 1, 1, 0],
  ![0, 1, 5, 0, 0, 1],
  ![0, 1, 5, 0, 1, 0],
  ![0, 1, 5, 1, 0, 0],
  ![1, 0, 4, 0, 1, 1],
  ![1, 0, 4, 1, 0, 1],
  ![1, 0, 4, 1, 1, 0],
  ![1, 0, 5, 0, 0, 1],
  ![1, 0, 5, 0, 1, 0],
  ![1, 0, 5, 1, 0, 0],
  ![1, 1, 4, 0, 0, 1],
  ![1, 1, 4, 0, 1, 0],
  ![1, 1, 4, 1, 0, 0],
  ![1, 1, 5, 0, 0, 0],
  ![0, 4, 0, 1, 1, 1],
  ![0, 4, 1, 0, 1, 1],
  ![0, 4, 1, 1, 0, 1],
  ![0, 4, 1, 1, 1, 0],
  ![0, 5, 0, 0, 1, 1],
  ![0, 5, 0, 1, 0, 1],
  ![0, 5, 0, 1, 1, 0],
  ![0, 5, 1, 0, 0, 1],
  ![0, 5, 1, 0, 1, 0],
  ![0, 5, 1, 1, 0, 0],
  ![1, 4, 0, 0, 1, 1],
  ![1, 4, 0, 1, 0, 1],
  ![1, 4, 0, 1, 1, 0],
  ![1, 4, 1, 0, 0, 1],
  ![1, 4, 1, 0, 1, 0],
  ![1, 4, 1, 1, 0, 0],
  ![1, 5, 0, 0, 0, 1],
  ![1, 5, 0, 0, 1, 0],
  ![1, 5, 0, 1, 0, 0],
  ![1, 5, 1, 0, 0, 0]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row122ProductMonomials_eq :
    productMonomials (degreeSevenProductSource ⟨122, by decide⟩).2
      (degreeSevenProductSource ⟨122, by decide⟩).1 =
      row122ProductMonomials := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row122_product_coefficients :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨122, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨122, by decide⟩).2
          (degreeSevenProductSource ⟨122, by decide⟩).1
          (degreeSevenRepresentative j) := by
  unfold productCoefficient
  rw [row122ProductMonomials_eq]
  decide

theorem row122_literalProduct_eq_encoded :
    degreeSevenLiteralProduct ⟨122, by decide⟩ =
      degreeSevenEncodedProduct ⟨122, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row122_product_coefficients

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
