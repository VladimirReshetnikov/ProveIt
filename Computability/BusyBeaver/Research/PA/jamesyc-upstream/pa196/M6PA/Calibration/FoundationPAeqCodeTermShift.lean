module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTermValidity
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termCode_isUTerm {t : V} (ht : IsUTerm ℒₒᵣ t) :
    IsUTerm Presentation.language (termCode t) := (termCode_valid ht.isSemiterm).isUTerm

theorem termVector_isUTermVec {k ts : V} (ht : IsUTermVec ℒₒᵣ k ts) :
    IsUTermVec Presentation.language k (termVector k ts) :=
  (termVector_valid ht.isSemitermVec).isUTerm

theorem termCode_shift {t : V} (ht : IsUTerm ℒₒᵣ t) :
    termCode (termShift ℒₒᵣ t)=termShift Presentation.language (termCode t) := by
  apply IsUTerm.induction 𝚺 (P:=fun t => termCode (termShift ℒₒᵣ t)=termShift Presentation.language (termCode t)) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i; simp
  · intro i; simp
  · intro k f ts hf hs ih
    have hv := termVector_isUTermVec hs
    have he : termVector k (termShiftVec ℒₒᵣ k ts)=termShiftVec Presentation.language k (termVector k ts) := by
      apply nth_ext' k (by simp [hs]) (by simp [hv])
      intro i hi
      rw [termVector_nth hs.termShiftVec hi,nth_termShiftVec hs hi,nth_termShiftVec hv hi,termVector_nth hs hi]
      exact ih i hi
    rw [termShift_func hf hs,termCode_func hf hs.termShiftVec,termCode_func hf hs,he]
    rcases (original_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp [functionCode,zeroCode,Presentation.source_functions]
    · simp [functionCode,oneCode,zeroCode,Presentation.source_functions]
    · simp [functionCode,termShift_func,Presentation.source_functions,hv]
    · simp [functionCode,termShift_func,Presentation.source_functions,hv]

theorem termVector_shift {k ts : V} (ht : IsUTermVec ℒₒᵣ k ts) :
    termVector k (termShiftVec ℒₒᵣ k ts)=termShiftVec Presentation.language k (termVector k ts) := by
  have hv := termVector_isUTermVec ht
  apply nth_ext' k (by simp [ht]) (by simp [hv])
  intro i hi
  rw [termVector_nth ht.termShiftVec hi,nth_termShiftVec ht hi,nth_termShiftVec hv hi,termVector_nth ht hi]
  exact termCode_shift (ht.nth hi)

#print axioms termCode_isUTerm
#print axioms termVector_isUTermVec
#print axioms termCode_shift
#print axioms termVector_shift
end M6.PA.FoundationPAeqCode
