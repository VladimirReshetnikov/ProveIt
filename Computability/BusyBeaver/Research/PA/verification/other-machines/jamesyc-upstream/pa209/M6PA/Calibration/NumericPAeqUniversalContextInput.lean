module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqGuardedUniversalInput
public import M6PA.Calibration.NumericPAeqExistentialRule
@[expose] public section
namespace M6.PA.NumericPAeqUniversalContext
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqInductionInterpretation RelationalSource.Numeric
open ActualCertificateConstructors.Dominated ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem freeDomain_prepend_requested_certificate {f x:V}
    (hf:IsSemitermVec language (len f) 0 f) (hx:IsSemiterm language 0 x)
    (native lo z:V) (hc:FormulaCovered 0 native lo z
      (imp language (qqAnd (freeDomain f) (domainCode x)) (freeDomain (x∷f)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp language (qqAnd (freeDomain f) (domainCode x)) (freeDomain (x∷f)))+1 :=by
  let param:=parameters 0 native lo z
  have hF:=freeDomain_valid hf
  have hD:=domainCode_isSemiformula hx
  have hnew:IsSemitermVec language (len (x∷f)) 0 (x∷f):=by simpa using hf.adjoin hx
  have hN:=freeDomain_valid hnew
  obtain ⟨code,hcode⟩:=NumericPAeqValueDomainGuard.guard_prepend_certificate param f (len f) 0 x
    (fun i hi=>hf.nth hi) hx
  have ha:translate param (qqAnd (freeDomain f) (domainCode x))=
      wa (translate param (freeDomain f)) (translate param (domainCode x)):=by
    rw [translate_and _ _ _ hF.isUFormula hD.isUFormula,translationAnd_eq]
  let arrow:Certificate (wim (translate param (qqAnd (freeDomain f) (domainCode x)))
      (translate param (freeDomain (x∷f)))):=⟨code,by rw [ha]; simpa [freeDomain] using hcode⟩
  obtain ⟨_,back,_,hback⟩:=translate_imp_certificates param _ _
    (IsSemiformula.and.mpr ⟨hF,hD⟩).isUFormula hN.isUFormula
  let out:=arrow.mp ⟨back,hback⟩
  exact ⟨out.code,out.accepted⟩
#print axioms freeDomain_prepend_requested_certificate
end M6.PA.NumericPAeqUniversalContext

