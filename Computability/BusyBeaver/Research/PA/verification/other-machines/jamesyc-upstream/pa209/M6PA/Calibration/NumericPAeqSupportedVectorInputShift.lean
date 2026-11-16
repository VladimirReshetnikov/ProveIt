module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedVectorRealizationSyntax
public import M6PA.Calibration.NumericPAeqValueDomainGuardTargetShift
public import M6PA.Calibration.NumericPAeqValueRealizationGuardTargetShift
@[expose] public section
namespace M6.PA.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem vectorEnvironment_targetShift {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t):
    SupportedVectorEnvironment s r (targetShiftTerms b) (targetShiftTerms f) (targetShiftTerms a) w t := by
  refine ⟨targetShiftTerms_valid h.1,?_,targetShiftTerms_valid h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_,?_⟩
  · simpa [targetShiftTerms_length h.2.1] using targetShiftTerms_valid h.2.1
  · simpa [targetShiftTerms_length h.2.1] using h.2.2.2.2.2.1
  · simpa [targetShiftTerms_length h.2.1] using h.2.2.2.2.2.2
theorem vectorInput_targetShift {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t):
    shift language (vectorInput s r b f a w)=
      vectorInput s r (targetShiftTerms b) (targetShiftTerms f) (targetShiftTerms a) w := by
  have hb := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.1
  have hf := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.1
  have ha := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.2.1
  have hg := NumericPAeqValueRealizationGuard.guard_isSemiformula b f w a s 0 (fun i hi=>entry_valid h hi)
  have hbf := (IsSemiformula.and.mpr ⟨hb,hf⟩).isUFormula
  have haf := (IsSemiformula.and.mpr ⟨ha,hf⟩).isUFormula
  have hrest := (IsSemiformula.and.mpr ⟨IsSemiformula.and.mpr ⟨ha,hf⟩,hg⟩).isUFormula
  simp only [vectorInput,inputDomain,shift_and hbf hrest,shift_and haf hg.isUFormula,
    shift_and hb.isUFormula hf.isUFormula,shift_and ha.isUFormula hf.isUFormula,
    NumericPAeqValueDomainGuard.guard_targetShift h.1 (le_refl r),
    NumericPAeqValueDomainGuard.guard_targetShift h.2.1 (le_refl (len f)),
    NumericPAeqValueDomainGuard.guard_targetShift h.2.2.1 (le_refl s),
    NumericPAeqValueRealizationGuard.guard_supported_targetShift h.1 h.2.1 h.2.2.2.2.1 h.2.2.1 h.2.2.2.2.2.2 (le_refl s),
    targetShiftTerms_length h.2.1]
#print axioms vectorEnvironment_targetShift
#print axioms vectorInput_targetShift
end M6.PA.NumericPAeqSupportedVectorRealization
