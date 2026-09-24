import Surreal.Algebra.RecursiveSaturation
import Surreal.Surcomplex.AlgebraicOmittedType

/-!
# The actual omnific rings are not recursively saturated

The recursive-saturation conclusion of `odg:def:thm:saturation` for the actual
universe-indexed real and Gaussian omnific integers. The witness is the explicit
computable native type already proved finitely satisfiable and omitted.
-/

universe u
namespace Surreal
open RecursiveSaturation

namespace Foundations.SignSequence
noncomputable local instance : FirstOrder.Ring.CompatibleRing OmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing OmnificInteger

/-- The actual real omnific integers fail recursive saturation. -/
theorem omnific_not_recursivelySaturated : ¬ RecursivelySaturated OmnificInteger.{u} :=
  not_recursivelySaturated_of_algebraicType ArithmeticGuards.integerGuard
    omnific_algebraicType_finitelySatisfiable omnific_algebraicType_omitted

end Foundations.SignSequence
namespace Surcomplex
noncomputable local instance : FirstOrder.Ring.CompatibleRing GaussianOmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing GaussianOmnificInteger

/-- The actual Gaussian omnific integers fail recursive saturation. -/
theorem gaussianOmnific_not_recursivelySaturated :
    ¬ RecursivelySaturated GaussianOmnificInteger.{u} :=
  not_recursivelySaturated_of_algebraicType ArithmeticGuards.integerGuard
    gaussianOmnific_algebraicType_finitelySatisfiable gaussianOmnific_algebraicType_omitted

end Surcomplex
end Surreal
