import PolynomialFormulas.LazardInvariantModularProductCoefficientCore

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

set_option autoImplicit false

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

/- Closed executable coefficient equality for one source-row block. -/
set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem degreeSevenProductRow_eq_productCoefficient_block_nine :
    ∀ i : Fin 159, 72 ≤ i.1 ∧ i.1 < 80 → ∀ j : Fin 132,
      degreeSevenProductRow i j =
        productCoefficient (degreeSevenProductSource i).2
          (degreeSevenProductSource i).1 (degreeSevenRepresentative j) := by
  decide

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
