module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateVariableCertificate
public import M6PA.Calibration.RelationalPredicateTemplateVariableConstructor
public import PA196.Arithmetic.Transport.NumericPAeqValueDomainGuardProjection
public import PA196.Arithmetic.Transport.FoundationRelationalSequentConnectiveNormalization
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate
open M6.PA.RelationalPredicateTemplate.Variable

namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate.Variable
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric NumericPAeqTerm
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

noncomputable def variableOutput (x : V) : V :=
  qqExs (variableValue (qqBvar 0) (termBShift L x))

theorem variableOutput_valid (x : V) (hx:IsSemiterm L 0 x) : IsFormula L (variableOutput x) := by
  apply IsSemiformula.exs.mpr
  exact variableValue_isSemiformula (by simp) (by simpa using hx.termBShift)

theorem variable_native_arrow (x g lo z : V) (hx:IsSemiterm L 0 x)
    (hc:FormulaCovered 0 g lo z (variableTotalityCode x)) :
    ∃code,verifyValue code=wim (translate (parameters 0 g lo z) (domainCode x))
      (translate (parameters 0 g lo z) (variableOutput x))+1 := by
  obtain ⟨code,hcode⟩ := variableTotality_requested_certificate x g lo z hx hc
  rw [variableTotalityCode_constructor x hx] at hcode
  obtain ⟨forward,backward,hf,_⟩ := translate_imp_certificates (parameters 0 g lo z)
    (domainCode x) (variableOutput x) (domainCode_isSemiformula hx).isUFormula
    (variableOutput_valid x hx).isUFormula
  let out := (⟨code,hcode⟩ : Certificate (translate (parameters 0 g lo z)
    (imp L (domainCode x) (variableOutput x)))).mp ⟨forward,hf⟩
  exact ⟨out.code,out.accepted⟩

theorem variable_from_guard_certificate (env k i g lo z : V) (hi:i<k)
    (h:∀j<k,IsSemiterm L 0 (nth env j))
    (hc:FormulaCovered 0 g lo z (variableTotalityCode (nth env i))) :
    ∃code,verifyValue code=wim
      (translate (parameters 0 g lo z) (NumericPAeqValueDomainGuard.guard env k))
      (translate (parameters 0 g lo z) (variableOutput (nth env i)))+1 := by
  obtain ⟨a,ha⟩ := NumericPAeqValueDomainGuard.guard_projection_certificate
    (parameters 0 g lo z) env k 0 i hi h
  obtain ⟨b,hb⟩ := variable_native_arrow (nth env i) g lo z (h i hi) hc
  let out := implicationCompose (⟨a,ha⟩) (⟨b,hb⟩)
  exact ⟨out.code,out.accepted⟩

#print axioms variableOutput_valid
#print axioms variable_native_arrow
#print axioms variable_from_guard_certificate
end PA196.Arithmetic.Transport.RelationalPredicateTemplate.Variable

