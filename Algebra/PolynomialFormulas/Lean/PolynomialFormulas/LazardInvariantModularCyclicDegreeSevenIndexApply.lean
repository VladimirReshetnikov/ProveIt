import PolynomialFormulas.LazardInvariantModularCyclicDegreeSevenIndex

/-! Transport from the executable orbit-list index to the literal index. -/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants

open LazardInvariantModularCounterexample
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

noncomputable section

@[simp]
theorem degreeSevenIndexEquivOrbitRepresentative_apply_val (i : Fin 132) :
    (degreeSevenIndexEquivOrbitRepresentative i).1 =
      degreeSevenRepresentative i := by
  rfl

end


end LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants
