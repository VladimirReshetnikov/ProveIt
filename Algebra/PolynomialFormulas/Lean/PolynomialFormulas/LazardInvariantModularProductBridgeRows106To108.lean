import PolynomialFormulas.LazardInvariantModularProductCoefficientCore

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

/- Closed executable coefficient equality for source rows `106, 107`. -/
set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem degreeSevenProductRow_eq_productCoefficient_rows_106_108 :
    ∀ i : Fin 159, 106 ≤ i.1 ∧ i.1 < 108 → ∀ j : Fin 132,
      degreeSevenProductRow i j =
        productCoefficient (degreeSevenProductSource i).2
          (degreeSevenProductSource i).1 (degreeSevenRepresentative j) := by
  decide

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
