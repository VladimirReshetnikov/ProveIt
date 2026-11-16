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
theorem edge_from : PrimitiveData.edge =
 Formula.fromFoundation (memRel : ArithmeticSemisentence 3) := by
 with_unfolding_all rfl
theorem edge_to : PrimitiveData.edge.toFoundation =
 (memRel : ArithmeticSemisentence 3) := by
 rw [edge_from,Formula.to_from]
#print axioms edge_to
end PalomarPA
