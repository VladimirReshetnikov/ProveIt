import PolynomialFormulas.LazardInvariantModularProductCoefficientCore

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

/- Closed executable coefficient equality for source rows `98, 99`. -/
set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem degreeSevenProductRow_eq_productCoefficient_rows_98_100 :
    ∀ i : Fin 159, 98 ≤ i.1 ∧ i.1 < 100 → ∀ j : Fin 132,
      degreeSevenProductRow i j =
        productCoefficient (degreeSevenProductSource i).2
          (degreeSevenProductSource i).1 (degreeSevenRepresentative j) := by
  decide

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
