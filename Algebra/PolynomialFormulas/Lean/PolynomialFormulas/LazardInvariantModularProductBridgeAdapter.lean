import PolynomialFormulas.LazardInvariantModularProductBridgeSemantics
import PolynomialFormulas.LazardInvariantModularProductCoefficientBridge

/-! Adapter from executable product-row certificates to polynomial equality. -/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

theorem degreeSevenProductSource_degree_lt_seven :
    ∀ i : Fin 159, (degreeSevenProductSource i).1 < 7 := by
  decide

/-- A closed row computation may use the original list-count coefficient
generator; the generic bridge turns it into the semantic hypothesis needed
by polynomial reconstruction. -/
theorem degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
    (i : Fin 159)
    (hrow : ∀ j : Fin 132,
      degreeSevenProductRow i j =
        productCoefficient (degreeSevenProductSource i).2
          (degreeSevenProductSource i).1 (degreeSevenRepresentative j)) :
    degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  apply degreeSevenLiteralProduct_eq_encoded_of_coefficients i
  intro j
  exact (hrow j).trans
    (productCoefficient_eq_semanticProductCoefficient
      (degreeSevenProductSource i).2 (degreeSevenRepresentative j)
      ⟨(degreeSevenProductSource i).1,
        degreeSevenProductSource_degree_lt_seven i⟩)

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
