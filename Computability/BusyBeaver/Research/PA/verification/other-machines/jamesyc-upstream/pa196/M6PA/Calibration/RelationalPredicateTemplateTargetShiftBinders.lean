module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateTargetShiftAtoms
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem targetShiftEnvironments_valid {s n b f : V} (h : EnvironmentsValid s n b f) :
    EnvironmentsValid s n (targetShiftTerms b) (targetShiftTerms f) := by
  exact ⟨NumericPAeqTerm.targetShiftTerms_valid h.1,
    by simpa [NumericPAeqTerm.targetShiftTerms_length h.2] using NumericPAeqTerm.targetShiftTerms_valid h.2⟩
theorem bindFree_targetShift {k n f : V} (h : IsSemitermVec RelationalSource.language k n f) :
    targetShiftTerms (bindFree f)=bindFree (targetShiftTerms f) :=
  NumericPAeqTerm.targetShiftTerms_shiftTerms h
theorem bindBound_targetShift {k n b : V} (h : IsSemitermVec RelationalSource.language k n b) :
    targetShiftTerms (bindBound b)=bindBound (targetShiftTerms b) := by
  have hs := NumericPAeqTerm.shiftTerms_isSemitermVec h
  have hc := NumericPAeqTerm.targetShiftTerms_shiftTerms h
  unfold bindBound
  simp only [NumericPAeqTerm.targetShiftTerms,len_adjoin]
  rw [NumericPAeqTerm.shiftTerms_length h,termShiftVec_cons (by simp) hs.isUTerm]
  simpa [NumericPAeqTerm.targetShiftTerms,NumericPAeqTerm.shiftTerms_length h] using congrArg (fun x : V => qqBvar 0∷x) hc
#print axioms targetShiftEnvironments_valid
#print axioms bindFree_targetShift
#print axioms bindBound_targetShift
end M6.PA.RelationalPredicateTemplate

