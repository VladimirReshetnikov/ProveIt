import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesCore

/-!
# Raw-enumeration bridge for the degree-seven representative table

This is the sole expensive check connecting the literal 132-entry table to
the executable canonical-orbit enumeration.  All pair-separation shards can
therefore reduce over the small literal table without trusting generated
data.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularOrbitCoordinates

open LazardInvariantModularCounterexample

set_option autoImplicit false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem degreeSevenRepresentativeList_eq_orbitRepresentatives :
    degreeSevenRepresentativeList = orbitRepresentatives 7 := by
  decide

/-- Pointwise form of the raw-enumeration bridge. -/
theorem degreeSevenRepresentative_eq_computed (i : Fin 132) :
    degreeSevenRepresentative i =
      (orbitRepresentatives 7).getD i.1 (fun _ => 0) := by
  rw [degreeSevenRepresentative,
    degreeSevenRepresentativeList_eq_orbitRepresentatives]

end LeanProofs.PolynomialFormulas.LazardInvariantModularOrbitCoordinates
