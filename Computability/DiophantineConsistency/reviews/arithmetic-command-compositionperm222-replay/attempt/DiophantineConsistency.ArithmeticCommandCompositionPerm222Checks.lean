import DiophantineConsistency.ArithmeticCommandCompositionPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandCompositionPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCommandAppendPerm222 ArithmeticCommandTickPerm222
open ArithmeticCommandRunPerm222 ArithmeticCommandCompositionPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (right w : V) : extendValue right (liveValue 0 w)=liveValue right w := extend_done right w
example (left right w : V) (h : evalValue left w=0) :
    evalValue (appendValue left right) w=0 := eval_append_halt left right w h
example (left right w result : V) (h : evalValue left w=result+1) :
    evalValue (appendValue left right) w=evalValue right result :=
  eval_append_success left right w result h
example (right w : V) : evalValue (appendValue 0 right) w=evalValue right w := by
  rw [appendValue_zero]
example (left w : V) : evalValue (appendValue left 0) w=evalValue left w := by
  rw [append_right_zero]

#print axioms extend_defined
#print axioms extend_zero
#print axioms extend_live
#print axioms extend_done
#print axioms tick_extend_succ
#print axioms tick_extend_active
#print axioms paired_or_stopped
#print axioms stopped_pair
#print axioms terminal_append
#print axioms eval_append
#print axioms eval_append_eq_zero
#print axioms eval_append_halt
#print axioms eval_append_success
end DiophantineConsistency.ArithmeticCommandCompositionPerm222Checks
