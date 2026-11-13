module
public import PrimitiveData
public import FoundationBridge
public import Foundation.FirstOrder.Arithmetic.HFS.Vec
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
theorem core_from : PrimitiveData.core =
 Formula.fromFoundation (Nth.blueprint.core.sigma : ArithmeticSemisentence 2) := by
 with_unfolding_all rfl
theorem core_to : PrimitiveData.core.toFoundation =
 (Nth.blueprint.core.sigma : ArithmeticSemisentence 2) := by
 rw [core_from,Formula.to_from]
#print axioms core_to
end PalomarPA
