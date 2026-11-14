import PA194PAeqTranslationShift
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_bShiftVec_valid {k ts : V} (ht : IsUTermVec ℒₒᵣ k ts) :
    IsUTermVec ℒₒᵣ k (termBShiftVec ℒₒᵣ k ts) := by
  refine ⟨(len_termBShiftVec ht).symm,?_⟩
  intro i hi
  rw [nth_termBShiftVec ht hi]
  exact (ht.nth hi).isSemiterm.termBShift.isUTerm

theorem termCode_bShift {t : V} (ht : IsUTerm ℒₒᵣ t) :
    termCode (termBShift ℒₒᵣ t)=termBShift PA194PAeq.language (termCode t) := by
  apply IsUTerm.induction 𝚺 (P:=fun t => termCode (termBShift ℒₒᵣ t)=termBShift PA194PAeq.language (termCode t)) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i; simp
  · intro i; simp
  · intro k f ts hf hs ih
    have hv := termVector_isUTermVec hs
    have he : termVector k (termBShiftVec ℒₒᵣ k ts)=termBShiftVec PA194PAeq.language k (termVector k ts) := by
      apply nth_ext' k (termVector_length (source_bShiftVec_valid hs)) (by simp [hv])
      intro i hi
      rw [termVector_nth (source_bShiftVec_valid hs) hi,nth_termBShiftVec hs hi,nth_termBShiftVec hv hi,termVector_nth hs hi]
      exact ih i hi
    rw [termBShift_func hf hs,termCode_func hf (source_bShiftVec_valid hs),termCode_func hf hs,he]
    rcases (original_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp [functionCode,zeroCode,PA194PAeq.source_functions]
    · simp [functionCode,oneCode,zeroCode,PA194PAeq.source_functions]
    · simp [functionCode,termBShift_func,PA194PAeq.source_functions,hv]
    · simp [functionCode,termBShift_func,PA194PAeq.source_functions,hv]

theorem termVector_bShift {k ts : V} (ht : IsUTermVec ℒₒᵣ k ts) :
    termVector k (termBShiftVec ℒₒᵣ k ts)=termBShiftVec PA194PAeq.language k (termVector k ts) := by
  have hv := termVector_isUTermVec ht
  apply nth_ext' k (termVector_length (source_bShiftVec_valid ht)) (by simp [hv])
  intro i hi
  rw [termVector_nth (source_bShiftVec_valid ht) hi,nth_termBShiftVec ht hi,nth_termBShiftVec hv hi,termVector_nth ht hi]
  exact termCode_bShift (ht.nth hi)

#print axioms source_bShiftVec_valid
#print axioms termCode_bShift
#print axioms termVector_bShift
end PA194PAeqTermBlueprint
