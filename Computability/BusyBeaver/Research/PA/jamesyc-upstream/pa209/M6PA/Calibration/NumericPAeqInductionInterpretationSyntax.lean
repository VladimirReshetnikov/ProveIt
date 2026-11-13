module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaZeroInstance
public import M6PA.Calibration.NumericPAeqFormulaSupportedOpening
public import M6PA.Calibration.NumericPAeqValueDomainGuardTargetShift
@[expose] public section
namespace M6.PA.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def freeDomain (f:V):V := NumericPAeqValueDomainGuard.guard f (len f)
noncomputable def property (f p:V):V := formulaSyntax (binderParameters (parameters 0 f)) p
noncomputable def zeroValue (f p:V):V := substitutedFormula 0 f ((qqFunc 0 0 0)∷0) p
noncomputable def zeroDomain : V := qqAnd (NumericPAeqTerm.domainCode (qqBvar 0)) (NumericPAeqTerm.zeroCode (qqBvar 0))
theorem zero_supported (l:V):NumericPAeqTerm.FreeSupported l (qqFunc 0 0 0) :=
  (NumericPAeqTerm.freeSupported_func (show Presentation.language.IsFunc (0:V) 0 by simp)
    (show IsUTermVec Presentation.language (0:V) 0 by simp)).mpr (by simp)
theorem property_covered {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    SupportedFormulaCovered 1 1 (binderParameters (parameters 0 f)) p := by
  have he : ParametersValid (0:V) 0 (parameters 0 f) := by simp [ParametersValid,hf]
  exact ⟨by simpa using binderParameters_valid he,hp,by
    simpa [binderParameters,NumericPAeqTerm.shiftTerms_zero_arity hf] using hs⟩
theorem property_valid {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    IsSemiformula language 1 (property f p) := formulaSyntax_supported_isSemiformula (property_covered hf hp hs)
theorem freeDomain_valid {f:V} (hf:IsSemitermVec language (len f) 0 f):IsFormula language (freeDomain f) :=
  NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf
theorem zeroValue_valid {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):IsFormula language (zeroValue f p) := by
  exact substitutedFormula_valid (singleton_environment ⟨hf,hp,by simp,hs,zero_supported _,show IsSemiterm language 0 (qqFvar (0:V)) by simp⟩)
theorem freeDomain_shift {f:V} (hf:IsSemitermVec language (len f) 0 f):
    shift language (freeDomain f)=freeDomain (targetShiftTerms f) := by
  simpa [freeDomain,targetShiftTerms_length hf] using NumericPAeqValueDomainGuard.guard_targetShift hf (le_refl (len f))
theorem zeroValue_shift {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    shift language (zeroValue f p)=zeroValue (targetShiftTerms f) p := by
  have he := singleton_environment ⟨hf,hp,by simp,hs,zero_supported _,show IsSemiterm language 0 (qqFvar (0:V)) by simp⟩
  simpa [zeroValue,NumericPAeqTerm.targetShiftTerms] using substitutedFormula_targetShift he
theorem property_free {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    free language (property f p)=originalFormula (qqFvar 0∷0) (targetShiftTerms f) p := by
  simpa [property,originalFormula,NumericPAeqTerm.targetShiftTerms] using
    formulaSyntax_supported_free_binder (show IsSemitermVec language (0:V) 0 0 by simp) hf (by simpa using hp) hs
theorem zeroDomain_valid : IsSemiformula language (1:V) zeroDomain :=
  IsSemiformula.and.mpr ⟨NumericPAeqTerm.domainCode_isSemiformula (by simp),NumericPAeqTerm.zeroCode_isSemiformula (by simp)⟩
theorem zeroDomain_free :free language (zeroDomain:V)=
    qqAnd (NumericPAeqTerm.domainCode (qqFvar 0)) (NumericPAeqTerm.zeroCode (qqFvar 0)) := by
  have hz : IsSemiterm language (1:V) (qqBvar 0) := by simp
  have hw : IsSemitermVec language (1:V) 0 (qqFvar 0∷0) := by simp
  rw [zeroDomain,free_and_code (NumericPAeqTerm.domainCode_isSemiformula hz) (NumericPAeqTerm.zeroCode_isSemiformula hz)]
  simp only [free,NumericPAeqTerm.domainCode_targetShift hz,NumericPAeqTerm.zeroCode_targetShift hz,termShift_bvar,substs1]
  rw [NumericPAeqTerm.domainCode_targetSubst hw hz,NumericPAeqTerm.zeroCode_targetSubst hw hz]
  simp
#print axioms property_valid
#print axioms zeroValue_valid
#print axioms freeDomain_shift
#print axioms zeroValue_shift
#print axioms property_free
#print axioms zeroDomain_free
end M6.PA.NumericPAeqInductionInterpretation

