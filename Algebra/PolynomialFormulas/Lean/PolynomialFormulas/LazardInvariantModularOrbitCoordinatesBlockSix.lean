import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesCore

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

/- Separates the canonical degree-seven orbit representatives in one row
block of the finite certificate. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem degreeSevenRepresentative_mem_orbit_iff_block_six :
    ∀ i j : Fin 132, 60 ≤ i.1 ∧ i.1 < 70 →
      (degreeSevenRepresentative j ∈
          cyclicOrbitSupport (degreeSevenRepresentative i) ↔ i = j) := by
  decide

end LeanProofs.PolynomialFormulas.LazardInvariantModularOrbitCoordinates
