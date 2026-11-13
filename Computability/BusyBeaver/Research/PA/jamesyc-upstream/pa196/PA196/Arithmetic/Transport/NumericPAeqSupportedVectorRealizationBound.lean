module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationProjection
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueUniqueness
public import PA196.Arithmetic.Transport.NumericPAeqSubstitutionVariableCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence NumericPAeqValueVectorRealization PA196.Arithmetic.Checker
open NumericPAeqSupportedValueTotality NumericPAeqSupportedValueCoherence
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem vector_bvar_certificate {s r b f a w i:V} (h:SupportedVectorEnvironment s r b f a w (qqBvar i))
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (vectorCode s r b f a w (qqBvar i))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (vectorCode s r b f a w (qqBvar i))+1 := by
  have hi := IsSemiterm.bvar.mp h.2.2.2.1
  have hu := entry_environment h hi
  let val := NumericPAeqValueRealizationGuard.entry b f w a i
  let cmp := comparisonCode b b f f (nth w i)
  have hval : IsFormula language val := entry_valid h hi
  have hcmp : IsFormula language cmp := NumericPAeqSupportedValueCoherence.comparisonCode_valid ⟨hu,hu⟩
  have hinst : substs1 language (nth a i) (valuePredicate b f (nth w i))=val := by
    exact valueSyntax_supported_bound_instance hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 (h.2.2.1.nth hi)
  have he : substitutionVariableCode (valuePredicate b f (nth w i)) (nth a i) =
      imp language (qqAnd val cmp) (vectorComparison b f a w (qqBvar i)) := by
    rw [substitutionVariableCode,hinst,←NumericPAeqSupportedValueCoherence.comparison_pairwise ⟨hu,hu⟩]
    simp [vectorComparison,valuePredicate,cmp]
  apply source_implication_compose _ (qqAnd val cmp) _ native lo z
    (vectorInput_valid h) (IsSemiformula.and.mpr ⟨hval,hcmp⟩) (vectorComparison_valid h) hc
  · intro native lo z hc
    apply source_implication_pair _ val cmp native lo z (vectorInput_valid h) hval hcmp hc
    · intro native lo z hc; exact vector_input_entry h hi native lo z hc
    · intro native lo z hc
      apply source_implication_compose _ (inputDomain r b f) _ native lo z
        (vectorInput_valid h) (NumericPAeqSupportedValueTotality.inputDomain_valid hu) hcmp hc
      · intro native lo z _; exact vector_input_domain h (RelationalSource.Numeric.parameters 0 native lo z)
      · intro native lo z hc; exact NumericPAeqSupportedValueCoherence.guarded_value_uniqueness_certificate hu native lo z hc
  · intro native lo z hc
    rw [←he] at hc ⊢
    exact substitutionVariable_requested_certificate _ _ native lo z
      (NumericPAeqSupportedValueCoherence.valuePredicate_valid hu) (h.2.2.1.nth hi) hc
#print axioms vector_bvar_certificate
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
