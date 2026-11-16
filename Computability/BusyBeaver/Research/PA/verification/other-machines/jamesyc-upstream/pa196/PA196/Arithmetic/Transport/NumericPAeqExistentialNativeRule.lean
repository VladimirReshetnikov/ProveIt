module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqExistentialRule
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation
open RelationalSource.Numeric PA196.Arithmetic.Checker
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem existentialRuleCode_valid {f p u:V} (hf:IsSemitermVec L (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u):
    IsFormula L (existentialRuleCode f p u) :=
  IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨freeDomain_valid hf,
    instanceFormula_valid hf hp hu hs hus⟩,existentialFormula_valid hf hp hs⟩

/-- Native contextual arrow. The free-domain assumption is retained, not asserted. -/
theorem existential_native_rule_certificate {f p u:V} (hf:IsSemitermVec L (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (existentialRuleCode f p u)):
    ∃code,verifyValue code=wim
      (wa (translate (parameters 0 native lo z) (freeDomain f))
        (translate (parameters 0 native lo z) (instanceFormula f p u)))
      (translate (parameters 0 native lo z) (existentialFormula f p))+1 :=by
  have hH:=(freeDomain_valid hf).isUFormula
  have hB:=(instanceFormula_valid hf hp hu hs hus).isUFormula
  have hC:=(existentialFormula_valid hf hp hs).isUFormula
  obtain ⟨code,hcode⟩:=existential_rule_requested_certificate hf hp hu hs hus native lo z hc
  obtain ⟨forward,_,hforward,_⟩:=translate_imp_certificates (parameters 0 native lo z)
    (qqAnd (freeDomain f) (instanceFormula f p u)) (existentialFormula f p) (by simp [hH,hB]) hC
  let out:Certificate (wim (translate (parameters 0 native lo z) (qqAnd (freeDomain f) (instanceFormula f p u)))
      (translate (parameters 0 native lo z) (existentialFormula f p))) :=
    (⟨code,hcode⟩ : Certificate (translate (parameters 0 native lo z) (existentialRuleCode f p u))).mp ⟨forward,hforward⟩
  refine ⟨out.code,?_⟩
  simpa only [translate_and _ _ _ hH hB,translationAnd_eq] using out.accepted
#print axioms existentialRuleCode_valid
#print axioms existential_native_rule_certificate
end PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation

