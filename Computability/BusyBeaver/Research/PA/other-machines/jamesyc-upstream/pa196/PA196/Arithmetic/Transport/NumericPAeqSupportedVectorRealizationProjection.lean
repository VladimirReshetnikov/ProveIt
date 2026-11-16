module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationSyntax
public import PA196.Arithmetic.Transport.NumericPAeqValueRealizationGuardProjection
public import PA196.Arithmetic.Transport.NumericPAeqValueSourceProjections
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence NumericPAeqValueVectorRealization
open NumericPAeqSupportedValueTotality NumericPAeqSupportedValueCoherence
open PA196.Arithmetic.Checker ActualCertificateEquivalence PA196.Arithmetic.Certificates.Dominated
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem vector_input_domain {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t) (param:V):
    ∃code,verifyValue code=RelationalSource.Numeric.translate param (imp language (vectorInput s r b f a w) (inputDomain r b f))+1 := by
  apply source_conjunction_projection param _ _
    (NumericPAeqSupportedValueTotality.inputDomain_valid (substituted_environment h)).isUFormula _ true
  exact (IsSemiformula.and.mp (vectorInput_valid h)).2.isUFormula

theorem vector_input_entry {s r b f a w t i:V} (h:SupportedVectorEnvironment s r b f a w t) (hi:i<s)
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (vectorInput s r b f a w) (NumericPAeqValueRealizationGuard.entry b f w a i))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (vectorInput s r b f a w) (NumericPAeqValueRealizationGuard.entry b f w a i))+1 := by
  let G := NumericPAeqValueRealizationGuard.guard b f w a s
  let B := qqAnd (inputDomain s a f) G
  have hG : IsFormula language G := NumericPAeqValueRealizationGuard.guard_isSemiformula b f w a s 0 (fun j hj=>entry_valid h hj)
  have hD := NumericPAeqSupportedValueTotality.inputDomain_valid (original_environment h)
  have hB : IsFormula language B := IsSemiformula.and.mpr ⟨hD,hG⟩
  apply source_implication_compose _ G _ native lo z (vectorInput_valid h) hG (entry_valid h hi) hc
  · intro native lo z hc
    apply source_implication_compose _ B _ native lo z (vectorInput_valid h) hB hG hc
    · intro native lo z _
      exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) _ _
        (NumericPAeqSupportedValueTotality.inputDomain_valid (substituted_environment h)).isUFormula hB.isUFormula false
    · intro native lo z _
      exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) _ _ hD.isUFormula hG.isUFormula false
  · intro native lo z _
    let param := RelationalSource.Numeric.parameters 0 native lo z
    obtain ⟨code,hcode⟩ := NumericPAeqValueRealizationGuard.guard_projection_certificate param b f w a s 0 i hi (fun j hj=>entry_valid h hj)
    obtain ⟨_,back,_,hback⟩ := RelationalSource.Numeric.translate_imp_certificates param G _ hG.isUFormula (entry_valid h hi).isUFormula
    let out := (⟨code,hcode⟩ : Certificate _).mp ⟨back,hback⟩
    exact ⟨out.code,out.accepted⟩
#print axioms vector_input_domain
#print axioms vector_input_entry
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
