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
theorem under_from : PrimitiveData.under =
 Formula.fromFoundation (underDef : ArithmeticSemisentence 2) := by
 with_unfolding_all rfl
theorem under_to : PrimitiveData.under.toFoundation =
 (underDef : ArithmeticSemisentence 2) := by
 rw [under_from,Formula.to_from]
#print axioms under_to
end PalomarPA
