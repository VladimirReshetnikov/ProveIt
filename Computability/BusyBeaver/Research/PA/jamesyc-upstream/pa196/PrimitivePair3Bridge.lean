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
theorem pair3_from : PrimitiveData.pair3 =
 Formula.fromFoundation (pair₃Def : ArithmeticSemisentence 4) := by
 with_unfolding_all rfl
theorem pair3_to : PrimitiveData.pair3.toFoundation =
 (pair₃Def : ArithmeticSemisentence 4) := by
 rw [pair3_from,Formula.to_from]
#print axioms pair3_to
end PalomarPA
