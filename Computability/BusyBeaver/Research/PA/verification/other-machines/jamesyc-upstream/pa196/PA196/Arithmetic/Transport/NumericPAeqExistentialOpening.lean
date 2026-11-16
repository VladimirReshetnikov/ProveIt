module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqInductionInterpretationSyntax
public import M6PA.Calibration.NumericPAeqTermSupportedTargetShift
public import M6PA.Calibration.NumericPAeqTermSupportedBoundInstance
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormulaRealization NumericPAeqInductionInterpretation NumericPAeqValueCoherence
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def instanceFormula (f p u:V):V :=substitutedFormula 0 f (u∷0) p
theorem instanceFormula_valid {f p u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u):
    IsFormula language (instanceFormula f p u) :=
  substitutedFormula_valid (singleton_environment ⟨hf,hp,hu,hs,hus,show IsSemiterm language 0 (qqFvar 0) by simp⟩)
theorem instanceFormula_shift {f p u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u):
    shift language (instanceFormula f p u)=instanceFormula (targetShiftTerms f) p u := by
  simpa [instanceFormula,NumericPAeqTerm.targetShiftTerms] using
    substitutedFormula_targetShift (singleton_environment ⟨hf,hp,hu,hs,hus,show IsSemiterm language 0 (qqFvar 0) by simp⟩)
theorem valuePredicate_covered {f u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language 0 u) (hs:NumericPAeqTerm.FreeSupported (len f) u):
    NumericPAeqTerm.SupportedTermCovered 0 1 (NumericPAeqTerm.parameters 0 f (qqBvar 0)) u := by
  have hf1:IsSemitermVec language (len f) 1 f :=by
    rw [←NumericPAeqTerm.shiftTerms_zero_arity hf]
    simpa only [NumericPAeqTerm.shiftTerms_length hf,zero_add] using NumericPAeqTerm.shiftTerms_isSemitermVec hf
  refine ⟨by simp [NumericPAeqTerm.ParametersValid,hf1],hu,by simpa using hs⟩
theorem valuePredicate_free {f u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language 0 u) (hs:NumericPAeqTerm.FreeSupported (len f) u):
    free language (valuePredicate 0 f u)=NumericPAeqTerm.valueSyntax
      (NumericPAeqTerm.parameters 0 (targetShiftTerms f) (qqFvar 0)) u := by
  have hc :=valuePredicate_covered hf hu hs
  have hf' :IsSemitermVec language (len (targetShiftTerms f)) 0 (targetShiftTerms f) :=by
    simpa [targetShiftTerms_length hf] using targetShiftTerms_valid hf
  have hs' :NumericPAeqTerm.FreeSupported (len (targetShiftTerms f)) u :=by simpa [targetShiftTerms_length hf] using hs
  unfold valuePredicate
  rw [free,NumericPAeqTerm.valueSyntax_supported_targetShift hc]
  have he :NumericPAeqTerm.targetShiftParameters (NumericPAeqTerm.parameters (0:V) f (qqBvar 0))=
      NumericPAeqTerm.parameters 0 (targetShiftTerms f) (qqBvar 0) :=by simp [NumericPAeqTerm.targetShiftParameters,NumericPAeqTerm.targetShiftTerms]
  rw [he]
  exact NumericPAeqTerm.valueSyntax_supported_bound_instance (n:=0) (by simp) hf' hu hs' (by simp)
#print axioms instanceFormula_valid
#print axioms instanceFormula_shift
#print axioms valuePredicate_covered
#print axioms valuePredicate_free
end PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation

