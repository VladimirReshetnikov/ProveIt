import PolynomialFormulas.LazardInvariantModularProductCoefficientCore

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

/- Closed executable coefficient equality for source rows `110, 111`. -/
set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem degreeSevenProductRow_eq_productCoefficient_rows_110_112 :
    ∀ i : Fin 159, 110 ≤ i.1 ∧ i.1 < 112 → ∀ j : Fin 132,
      degreeSevenProductRow i j =
        productCoefficient (degreeSevenProductSource i).2
          (degreeSevenProductSource i).1 (degreeSevenRepresentative j) := by
  decide

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
