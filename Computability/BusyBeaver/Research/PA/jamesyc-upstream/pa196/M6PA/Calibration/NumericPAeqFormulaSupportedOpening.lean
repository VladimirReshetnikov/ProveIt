module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedTargetShift
public import M6PA.Calibration.NumericPAeqFormulaSupportedTargetSubst
public import M6PA.Calibration.RelationalPredicateTemplateSourceInstance
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length shiftTerms shiftTerms_length)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem targetShiftParameters_supported_covered {s n param p : V} (h : SupportedFormulaCovered s n param p) :
    SupportedFormulaCovered s n (targetShiftParameters param) p := by
  exact ⟨targetShiftParameters_valid h.1,h.2.1,by simpa [targetShiftParameters,targetShiftTerms_length h.1.2] using h.2.2⟩

theorem targetSubstParameters_open_binder {s b f x : V}
    (hb : IsSemitermVec language s 0 b) (hf : IsSemitermVec language (len f) 0 f) :
    targetSubstParameters (x∷0) (binderParameters (parameters b f))=parameters (x∷b) f := by
  have hbs : IsSemitermVec language (len b) 0 b := by simpa [hb.lh] using hb
  simp only [targetSubstParameters,binderParameters,parameters_bound,parameters_free]
  have hcons : RelationalPredicateTemplate.substTerms (x∷0) (qqBvar 0∷shiftTerms b)=
      x∷RelationalPredicateTemplate.substTerms (x∷0) (shiftTerms b) := by
    simp [RelationalPredicateTemplate.substTerms,NumericPAeqTerm.shiftTerms_length hb,
      termSubstVec_cons (show IsUTerm language (qqBvar (0:V)) by simp)
        (NumericPAeqTerm.shiftTerms_isSemitermVec hb).isUTerm]
  rw [hcons]
  rw [show RelationalPredicateTemplate.substTerms (x∷0) (shiftTerms b)=b from
    RelationalPredicateTemplate.source_instance_bindFree x hbs,
    show RelationalPredicateTemplate.substTerms (x∷0) (shiftTerms f)=f from
    RelationalPredicateTemplate.source_instance_bindFree x hf]

theorem formulaSyntax_supported_free_binder {s b f p : V}
    (hb : IsSemitermVec language s 0 b) (hf : IsSemitermVec language (len f) 0 f)
    (hp : IsSemiformula Presentation.language (s+1) p) (hs : FreeSupported (len f) p) :
    free language (formulaSyntax (binderParameters (parameters b f)) p)=
      formulaSyntax (parameters (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)) p := by
  have hen : ParametersValid s 0 (parameters b f) := by simpa [ParametersValid] using And.intro hb hf
  have hc : SupportedFormulaCovered (s+1) 1 (binderParameters (parameters b f)) p := by
    refine ⟨by simpa using binderParameters_valid hen,hp,?_⟩
    simpa [binderParameters,shiftTerms_length hf] using hs
  unfold free substs1
  rw [formulaSyntax_supported_targetShift hc]
  have hc' := targetShiftParameters_supported_covered hc
  rw [formulaSyntax_supported_targetSubst hc' (show IsSemitermVec language 1 0 (qqFvar 0∷(0:V)) by simp)]
  rw [targetShiftParameters_binder hen]
  simp only [targetShiftParameters,parameters_bound,parameters_free]
  change formulaSyntax (targetSubstParameters (qqFvar 0∷0)
    (binderParameters (parameters (targetShiftTerms b) (targetShiftTerms f)))) p=_
  rw [targetSubstParameters_open_binder (targetShiftTerms_valid hb)
    (by simpa [targetShiftTerms_length hf] using targetShiftTerms_valid hf)]
#print axioms targetShiftParameters_supported_covered
#print axioms targetSubstParameters_open_binder
#print axioms formulaSyntax_supported_free_binder
end M6.PA.NumericPAeqFormula

