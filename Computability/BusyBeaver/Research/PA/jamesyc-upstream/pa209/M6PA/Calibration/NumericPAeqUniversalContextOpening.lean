module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqUniversalContextOpeningSupport
public import M6PA.Calibration.NumericPAeqFormulaSupportedSourceFree
public import M6PA.Calibration.NumericPAeqInductionInterpretationSyntax
@[expose] public section
namespace M6.PA.NumericPAeqUniversalContextOpening
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def eigenEnvironment (f:V):V := qqFvar 0∷targetShiftTerms f
 theorem eigenEnvironment_valid {f:V} (hf:IsSemitermVec language (len f) 0 f):
    IsSemitermVec language (len (eigenEnvironment f)) 0 (eigenEnvironment f) := by
  simpa [eigenEnvironment,targetShiftTerms_length hf] using
    (targetShiftTerms_valid hf).adjoin (show IsSemiterm language (0:V) (qqFvar 0) by simp)
 theorem source_free_support {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    FreeSupported (len (eigenEnvironment f)) (free Presentation.language p) := by
  simpa [eigenEnvironment,targetShiftTerms_length hf] using freeSupported_free hp hs
 theorem source_free_covered {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    SupportedFormulaCovered 0 0 (parameters 0 (eigenEnvironment f)) (free Presentation.language p) := by
  refine ⟨?_,hp.free,?_⟩
  · simpa [ParametersValid] using eigenEnvironment_valid hf
  · simpa using source_free_support hf hp hs
 theorem source_shift_covered {f q:V} (hf:IsSemitermVec language (len f) 0 f)
    (hq:IsFormula Presentation.language q) (hs:FreeSupported (len f) q):
    SupportedFormulaCovered 0 0 (parameters 0 (eigenEnvironment f)) (shift Presentation.language q) := by
  refine ⟨?_,hq.shift,?_⟩
  · simpa [ParametersValid] using eigenEnvironment_valid hf
  · simpa [eigenEnvironment,targetShiftTerms_length hf] using freeSupported_shift hs
 theorem source_free_property {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    formulaSyntax (parameters 0 (eigenEnvironment f)) (free Presentation.language p)=
      free language (NumericPAeqInductionInterpretation.property f p) := by
  have h : SupportedFormulaCovered 1 0 (parameters (qqFvar 0∷0) (targetShiftTerms f)) p := by
    refine ⟨?_,hp,?_⟩
    · simp only [ParametersValid,parameters_bound,parameters_free]
      exact ⟨by simp,by simpa [targetShiftTerms_length hf] using targetShiftTerms_valid hf⟩
    · simpa [targetShiftTerms_length hf] using hs
  rw [show eigenEnvironment f=qqFvar 0∷targetShiftTerms f from rfl,
    formulaSyntax_supported_free_singleton h]
  symm
  simpa [NumericPAeqInductionInterpretation.property,NumericPAeqTerm.targetShiftTerms] using
    formulaSyntax_supported_free_binder (show IsSemitermVec language (0:V) 0 0 by simp) hf (by simpa using hp) hs
#print axioms source_free_support
#print axioms source_free_covered
#print axioms source_shift_covered
#print axioms source_free_property
end M6.PA.NumericPAeqUniversalContextOpening

