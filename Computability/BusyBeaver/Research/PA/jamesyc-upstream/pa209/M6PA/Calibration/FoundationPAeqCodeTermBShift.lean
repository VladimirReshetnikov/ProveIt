module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTermShift
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termCode_bShift {t : V} (ht : IsUTerm ℒₒᵣ t) :
    termCode (termBShift ℒₒᵣ t)=termBShift Presentation.language (termCode t) := by
  apply IsUTerm.induction 𝚺 (P:=fun t => termCode (termBShift ℒₒᵣ t)=termBShift Presentation.language (termCode t)) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i; simp
  · intro i; simp
  · intro k f ts hf hs ih
    have hv := termVector_isUTermVec hs
    have he : termVector k (termBShiftVec ℒₒᵣ k ts)=termBShiftVec Presentation.language k (termVector k ts) := by
      apply nth_ext' k (termVector_length hs.termBShiftVec) (by simp [hv])
      intro i hi
      rw [termVector_nth hs.termBShiftVec hi,nth_termBShiftVec hs hi,nth_termBShiftVec hv hi,termVector_nth hs hi]
      exact ih i hi
    rw [termBShift_func hf hs,termCode_func hf hs.termBShiftVec,termCode_func hf hs,he]
    rcases (original_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp [functionCode,zeroCode,Presentation.source_functions]
    · simp [functionCode,oneCode,zeroCode,Presentation.source_functions]
    · simp [functionCode,termBShift_func,Presentation.source_functions,hv]
    · simp [functionCode,termBShift_func,Presentation.source_functions,hv]

theorem termVector_bShift {k ts : V} (ht : IsUTermVec ℒₒᵣ k ts) :
    termVector k (termBShiftVec ℒₒᵣ k ts)=termBShiftVec Presentation.language k (termVector k ts) := by
  have hv := termVector_isUTermVec ht
  apply nth_ext' k (termVector_length ht.termBShiftVec) (by simp [hv])
  intro i hi
  rw [termVector_nth ht.termBShiftVec hi,nth_termBShiftVec ht hi,nth_termBShiftVec hv hi,termVector_nth ht hi]
  exact termCode_bShift (ht.nth hi)

#print axioms termCode_bShift
#print axioms termVector_bShift
end M6.PA.FoundationPAeqCode
