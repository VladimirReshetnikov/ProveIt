import PA194PAeqTranslationBShift
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termVector_qVec {k w : V} (hw : IsUTermVec ℒₒᵣ k w) :
    termVector (k+1) (qVec ℒₒᵣ w)=qVec PA194PAeq.language (termVector k w) := by
  simp only [qVec,termVector_length hw,←hw.lh]
  rw [termVector_cons (by simp) (source_bShiftVec_valid hw),termCode_bvar,termVector_bShift hw]

#print axioms termVector_qVec
end PA194PAeqTermBlueprint
