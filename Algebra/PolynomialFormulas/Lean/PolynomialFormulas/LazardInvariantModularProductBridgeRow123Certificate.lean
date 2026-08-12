import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

def row123ProductMonomials : List Exponent := [
  ![1,3,0,1,1,1],
  ![1,3,1,0,1,1],
  ![1,3,1,1,0,1],
  ![1,3,1,1,1,0],
  ![1,4,0,0,1,1],
  ![1,4,0,1,0,1],
  ![1,4,0,1,1,0],
  ![1,4,1,0,0,1],
  ![1,4,1,0,1,0],
  ![1,4,1,1,0,0],
  ![2,3,0,0,1,1],
  ![2,3,0,1,0,1],
  ![2,3,0,1,1,0],
  ![2,3,1,0,0,1],
  ![2,3,1,0,1,0],
  ![2,3,1,1,0,0],
  ![2,4,0,0,0,1],
  ![2,4,0,0,1,0],
  ![2,4,0,1,0,0],
  ![2,4,1,0,0,0],
  ![3,0,0,1,1,2],
  ![3,0,1,0,1,2],
  ![3,0,1,1,0,2],
  ![3,0,1,1,1,1],
  ![3,1,0,0,1,2],
  ![3,1,0,1,0,2],
  ![3,1,0,1,1,1],
  ![3,1,1,0,0,2],
  ![3,1,1,0,1,1],
  ![3,1,1,1,0,1],
  ![4,0,0,0,1,2],
  ![4,0,0,1,0,2],
  ![4,0,0,1,1,1],
  ![4,0,1,0,0,2],
  ![4,0,1,0,1,1],
  ![4,0,1,1,0,1],
  ![4,1,0,0,0,2],
  ![4,1,0,0,1,1],
  ![4,1,0,1,0,1],
  ![4,1,1,0,0,1],
  ![0,0,0,1,2,4],
  ![0,0,1,0,2,4],
  ![0,0,1,1,1,4],
  ![0,0,1,1,2,3],
  ![0,1,0,0,2,4],
  ![0,1,0,1,1,4],
  ![0,1,0,1,2,3],
  ![0,1,1,0,1,4],
  ![0,1,1,0,2,3],
  ![0,1,1,1,1,3],
  ![1,0,0,0,2,4],
  ![1,0,0,1,1,4],
  ![1,0,0,1,2,3],
  ![1,0,1,0,1,4],
  ![1,0,1,0,2,3],
  ![1,0,1,1,1,3],
  ![1,1,0,0,1,4],
  ![1,1,0,0,2,3],
  ![1,1,0,1,1,3],
  ![1,1,1,0,1,3],
  ![0,0,0,2,4,1],
  ![0,0,1,1,4,1],
  ![0,0,1,2,3,1],
  ![0,0,1,2,4,0],
  ![0,1,0,1,4,1],
  ![0,1,0,2,3,1],
  ![0,1,0,2,4,0],
  ![0,1,1,1,3,1],
  ![0,1,1,1,4,0],
  ![0,1,1,2,3,0],
  ![1,0,0,1,4,1],
  ![1,0,0,2,3,1],
  ![1,0,0,2,4,0],
  ![1,0,1,1,3,1],
  ![1,0,1,1,4,0],
  ![1,0,1,2,3,0],
  ![1,1,0,1,3,1],
  ![1,1,0,1,4,0],
  ![1,1,0,2,3,0],
  ![1,1,1,1,3,0],
  ![0,0,1,4,1,1],
  ![0,0,2,3,1,1],
  ![0,0,2,4,0,1],
  ![0,0,2,4,1,0],
  ![0,1,1,3,1,1],
  ![0,1,1,4,0,1],
  ![0,1,1,4,1,0],
  ![0,1,2,3,0,1],
  ![0,1,2,3,1,0],
  ![0,1,2,4,0,0],
  ![1,0,1,3,1,1],
  ![1,0,1,4,0,1],
  ![1,0,1,4,1,0],
  ![1,0,2,3,0,1],
  ![1,0,2,3,1,0],
  ![1,0,2,4,0,0],
  ![1,1,1,3,0,1],
  ![1,1,1,3,1,0],
  ![1,1,1,4,0,0],
  ![1,1,2,3,0,0],
  ![0,1,3,1,1,1],
  ![0,1,4,0,1,1],
  ![0,1,4,1,0,1],
  ![0,1,4,1,1,0],
  ![0,2,3,0,1,1],
  ![0,2,3,1,0,1],
  ![0,2,3,1,1,0],
  ![0,2,4,0,0,1],
  ![0,2,4,0,1,0],
  ![0,2,4,1,0,0],
  ![1,1,3,0,1,1],
  ![1,1,3,1,0,1],
  ![1,1,3,1,1,0],
  ![1,1,4,0,0,1],
  ![1,1,4,0,1,0],
  ![1,1,4,1,0,0],
  ![1,2,3,0,0,1],
  ![1,2,3,0,1,0],
  ![1,2,3,1,0,0],
  ![1,2,4,0,0,0]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row123ProductMonomials_eq :
    productMonomials (degreeSevenProductSource ⟨123, by decide⟩).2
      (degreeSevenProductSource ⟨123, by decide⟩).1 =
      row123ProductMonomials := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row123_product_coefficients :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨123, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨123, by decide⟩).2
          (degreeSevenProductSource ⟨123, by decide⟩).1
          (degreeSevenRepresentative j) := by
  unfold productCoefficient
  rw [row123ProductMonomials_eq]
  decide

theorem row123_literalProduct_eq_encoded :
    degreeSevenLiteralProduct ⟨123, by decide⟩ =
      degreeSevenEncodedProduct ⟨123, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row123_product_coefficients

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
