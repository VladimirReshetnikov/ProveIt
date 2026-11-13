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
theorem member_from : PrimitiveData.member =
 Formula.fromFoundation ((“x y. x ∈ y”) : ArithmeticSemisentence 2) := by
 with_unfolding_all rfl
theorem member_to : PrimitiveData.member.toFoundation =
 ((“x y. x ∈ y”) : ArithmeticSemisentence 2) := by
 rw [member_from,Formula.to_from]
#print axioms member_to
end PalomarPA
