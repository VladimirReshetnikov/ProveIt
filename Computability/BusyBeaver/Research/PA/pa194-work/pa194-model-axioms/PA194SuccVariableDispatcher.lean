import PA194TermDispatcherEquations
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SuccVariableDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def succVariablePacket (x z : V) : V := parameters (?[ ^&x] : V) 0 (^&z)

theorem translate_succVariable (x z : V) :
    translate (succVariablePacket x z) (^func (1 : V) 1 (?[ ^#(0 : V)] : V)) =
      successorValue (^&z) (variableValue (^#(0 : V)) (^&x)) := by
  have hv : IsSemitermVec SourceL (1 : V) (0 : V) (?[ ^&x] : V) := by simp
  rw [translate_succ _ _ (by simp),translate_bound]
  simp only [succVariablePacket,childParameters,parameters_bound,parameters_result]
  rw [shiftTerms_nth hv (by simp)]
  simp

#print axioms translate_succVariable
end generic
end PA194SuccVariableDispatcher
