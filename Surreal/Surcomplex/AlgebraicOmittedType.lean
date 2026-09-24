import Surreal.Algebra.AlgebraicOmittedType
import Surreal.Surcomplex.DiophantineConstants

/-!
# Omission of the explicit algebraic type in the actual omnific rings

Finite satisfiability and omission in `odg:def:thm:saturation`, independently
on the actual universe-indexed real and Gaussian omnific carriers. These are
native parameter-free ring formulas. The computability and recursive-saturation
clauses are not asserted here.
-/

universe u
namespace Surreal
open FirstOrder FirstOrder.Language AlgebraicOmittedType
noncomputable section

namespace Foundations.SignSequence
local instance omittedTypeOmnificStructure : FirstOrder.Ring.CompatibleRing OmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing OmnificInteger

/-- Every finite subset of the explicit type has an actual omnific realization. -/
theorem omnific_algebraicType_finitelySatisfiable :
    FinitelySatisfiable OmnificInteger.{u} (formulas ArithmeticGuards.integerGuard) :=
  xi_finitelySatisfiable

/-- No actual omnific integer realizes the whole explicit type. -/
theorem omnific_algebraicType_omitted :
    ¬ ∃ x : OmnificInteger.{u}, Realizes (formulas ArithmeticGuards.integerGuard) x := by
  apply xi_omitted_of_range omnificIntCast
  · intro x hx
    obtain ⟨a, ha⟩ := (omnific_xi_iff x).mp hx
    exact ⟨a, ha.symm⟩
  · intro a
    exact isAlgebraic_algebraMap a

end Foundations.SignSequence
namespace Surcomplex
local instance omittedTypeGaussianStructure : FirstOrder.Ring.CompatibleRing GaussianOmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing GaussianOmnificInteger

/-- Every finite subset also has an actual Gaussian omnific realization. -/
theorem gaussianOmnific_algebraicType_finitelySatisfiable :
    FinitelySatisfiable GaussianOmnificInteger.{u} (formulas ArithmeticGuards.integerGuard) :=
  xi_finitelySatisfiable

/-- No actual Gaussian omnific integer realizes the whole explicit type. -/
theorem gaussianOmnific_algebraicType_omitted :
    ¬ ∃ x : GaussianOmnificInteger.{u}, Realizes (formulas ArithmeticGuards.integerGuard) x := by
  apply xi_omitted_of_range gaussianOmnificConstants
  · intro x hx
    obtain ⟨a, ha⟩ := (gaussianOmnific_xi_iff x).mp hx
    exact ⟨a, ha.symm⟩
  · exact zsqrtd_isAlgebraic (-1)

end Surcomplex
end
end Surreal
