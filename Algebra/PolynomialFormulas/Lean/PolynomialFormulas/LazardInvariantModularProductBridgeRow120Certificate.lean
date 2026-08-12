import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

def row120ProductMonomials : List Exponent := [
  ![2,0,1,1,2,1],
  ![2,0,1,2,1,1],
  ![2,0,1,2,2,0],
  ![2,0,2,1,1,1],
  ![2,0,2,1,2,0],
  ![2,0,2,2,1,0],
  ![2,1,1,1,1,1],
  ![2,1,1,1,2,0],
  ![2,1,1,2,1,0],
  ![2,1,2,1,1,0],
  ![3,0,1,1,1,1],
  ![3,0,1,1,2,0],
  ![3,0,1,2,1,0],
  ![3,0,2,1,1,0],
  ![3,1,1,1,1,0],
  ![0,1,1,1,1,3],
  ![0,1,1,2,0,3],
  ![0,1,1,2,1,2],
  ![0,1,2,1,0,3],
  ![0,1,2,1,1,2],
  ![0,1,2,2,0,2],
  ![0,2,1,1,0,3],
  ![0,2,1,1,1,2],
  ![0,2,1,2,0,2],
  ![0,2,2,1,0,2],
  ![1,1,1,1,0,3],
  ![1,1,1,1,1,2],
  ![1,1,1,2,0,2],
  ![1,1,2,1,0,2],
  ![1,2,1,1,0,2],
  ![1,1,1,0,3,1],
  ![1,1,1,1,2,1],
  ![1,1,1,1,3,0],
  ![1,1,2,0,2,1],
  ![1,1,2,0,3,0],
  ![1,1,2,1,2,0],
  ![1,2,1,0,2,1],
  ![1,2,1,0,3,0],
  ![1,2,1,1,2,0],
  ![1,2,2,0,2,0],
  ![2,1,1,0,2,1],
  ![2,1,1,0,3,0],
  ![2,1,1,1,2,0],
  ![2,1,2,0,2,0],
  ![2,2,1,0,2,0],
  ![1,1,0,2,1,2],
  ![1,1,0,3,0,2],
  ![1,1,0,3,1,1],
  ![1,1,1,2,0,2],
  ![1,1,1,2,1,1],
  ![1,1,1,3,0,1],
  ![1,2,0,2,0,2],
  ![1,2,0,2,1,1],
  ![1,2,0,3,0,1],
  ![1,2,1,2,0,1],
  ![2,1,0,2,0,2],
  ![2,1,0,2,1,1],
  ![2,1,0,3,0,1],
  ![2,1,1,2,0,1],
  ![2,2,0,2,0,1],
  ![1,0,2,0,2,2],
  ![1,0,2,1,1,2],
  ![1,0,2,1,2,1],
  ![1,0,3,0,1,2],
  ![1,0,3,0,2,1],
  ![1,0,3,1,1,1],
  ![1,1,2,0,1,2],
  ![1,1,2,0,2,1],
  ![1,1,2,1,1,1],
  ![1,1,3,0,1,1],
  ![2,0,2,0,1,2],
  ![2,0,2,0,2,1],
  ![2,0,2,1,1,1],
  ![2,0,3,0,1,1],
  ![2,1,2,0,1,1],
  ![0,2,0,1,2,2],
  ![0,2,0,2,1,2],
  ![0,2,0,2,2,1],
  ![0,2,1,1,1,2],
  ![0,2,1,1,2,1],
  ![0,2,1,2,1,1],
  ![0,3,0,1,1,2],
  ![0,3,0,1,2,1],
  ![0,3,0,2,1,1],
  ![0,3,1,1,1,1],
  ![1,2,0,1,1,2],
  ![1,2,0,1,2,1],
  ![1,2,0,2,1,1],
  ![1,2,1,1,1,1],
  ![1,3,0,1,1,1]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row120ProductMonomials_eq :
    productMonomials (degreeSevenProductSource ⟨120, by decide⟩).2
      (degreeSevenProductSource ⟨120, by decide⟩).1 =
      row120ProductMonomials := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row120_product_coefficients :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨120, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨120, by decide⟩).2
          (degreeSevenProductSource ⟨120, by decide⟩).1
          (degreeSevenRepresentative j) := by
  unfold productCoefficient
  rw [row120ProductMonomials_eq]
  decide

theorem row120_literalProduct_eq_encoded :
    degreeSevenLiteralProduct ⟨120, by decide⟩ =
      degreeSevenEncodedProduct ⟨120, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row120_product_coefficients

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
