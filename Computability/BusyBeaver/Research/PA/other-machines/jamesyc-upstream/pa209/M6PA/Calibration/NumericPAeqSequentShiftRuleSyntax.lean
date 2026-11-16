module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqUniversalContextOpeningSupport
public import M6PA.Calibration.NumericPAeqSequentDerivationInvariant
public import M6PA.Calibration.NumericPAeqFormulaSupportedSourceShift
public import M6PA.Calibration.NumericPAeqValueDomainGuardCollection
@[expose] public section
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation
open ActualCertificateConstructors ActualCertificateConstructors.Dominated ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource.Numeric (translate)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem SupportedSet.prependShift {f s x:V} (hf:IsSemitermVec language (len f) 0 f)
    (hx:IsSemiterm language 0 x) (hs:SupportedSet (parameters 0 f) s):
    SupportedSet (parameters 0 (x∷f)) (setShift Presentation.language s) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_setShift_iff.mp hq
  have h := hs p hp
  refine ⟨?_,h.2.1.shift,?_⟩
  · simpa [ParametersValid] using hf.adjoin hx
  · simpa using freeSupported_shift (show FreeSupported (len f) p by simpa using h.2.2)
theorem prepend_shift_forward_certificate (native f s x:V)
    (hf:IsSemitermVec language (len f) 0 f) (hx:IsSemiterm language 0 x)
    (hs:SupportedSet (parameters 0 f) s):
    ∃code,verifyValue code=wim (translate native (sequentCode (parameters 0 f) s))
      (translate native (sequentCode (parameters 0 (x∷f)) (setShift Presentation.language s)))+1 := by
  apply sequent_eliminate_certificate native _ _ _ hs
  intro p hp
  obtain ⟨code,hcode⟩ := member_certificate native (parameters 0 (x∷f)) (setShift Presentation.language s)
    (shift Presentation.language p) (hs.prependShift hf hx) (shift_mem_setShift hp)
  rw [formulaSyntax_supported_sourceShift_parameters (hs p hp) hx] at hcode
  exact ⟨code,hcode⟩
theorem prepend_shift_backward_certificate (native f s x:V)
    (hf:IsSemitermVec language (len f) 0 f) (hx:IsSemiterm language 0 x)
    (hs:SupportedSet (parameters 0 f) s):
    ∃code,verifyValue code=wim (translate native (sequentCode (parameters 0 (x∷f)) (setShift Presentation.language s)))
      (translate native (sequentCode (parameters 0 f) s))+1 := by
  apply sequent_eliminate_certificate native _ _ _ (hs.prependShift hf hx)
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_setShift_iff.mp hq
  rw [formulaSyntax_supported_sourceShift_parameters (hs p hp) hx]
  exact member_certificate native _ s p hs hp
theorem freeDomain_tail_certificate (native f x:V)
    (hf:IsSemitermVec language (len f) 0 f) (hx:IsSemiterm language 0 x):
    ∃code,verifyValue code=wim (translate native (freeDomain (x∷f))) (translate native (freeDomain f))+1 := by
  apply NumericPAeqValueDomainGuard.guard_collection_certificate _ native f (len f) 0 (fun i hi=>hf.nth hi)
  intro i hi
  obtain ⟨code,hcode⟩ := NumericPAeqValueDomainGuard.guard_projection_certificate native (x∷f) (len f+1) 0 (i+1)
    (by simpa using hi) (fun j hj=>(hf.adjoin hx).nth hj)
  refine ⟨code,?_⟩
  simpa [freeDomain] using hcode
#print axioms SupportedSet.prependShift
#print axioms prepend_shift_forward_certificate
#print axioms prepend_shift_backward_certificate
#print axioms freeDomain_tail_certificate
end M6.PA.NumericPAeqFormula.Sequent

