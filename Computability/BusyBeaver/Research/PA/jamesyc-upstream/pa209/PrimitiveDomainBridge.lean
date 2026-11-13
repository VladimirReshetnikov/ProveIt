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
theorem domain_from : PrimitiveData.domain =
 Formula.fromFoundation (domainDef : ArithmeticSemisentence 2) := by
 with_unfolding_all rfl
theorem domain_to : PrimitiveData.domain.toFoundation =
 (domainDef : ArithmeticSemisentence 2) := by
 rw [domain_from,Formula.to_from]
#print axioms domain_to
end PalomarPA
