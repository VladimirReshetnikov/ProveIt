module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedVectorRealizationProjection
public import M6PA.Calibration.NumericPAeqSupportedValueTotality
@[expose] public section
namespace M6.PA.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization
open NumericPAeqSupportedValueTotality NumericPAeqValueCoherence ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem vector_input_original_domain {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t)
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (vectorInput s r b f a w) (inputDomain s a f))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (vectorInput s r b f a w) (inputDomain s a f))+1 := by
  let G := NumericPAeqValueRealizationGuard.guard b f w a s
  let R := qqAnd (inputDomain s a f) G
  have hd := NumericPAeqSupportedValueTotality.inputDomain_valid (original_environment h)
  have hg := NumericPAeqValueRealizationGuard.guard_isSemiformula b f w a s 0 (fun i hi=>entry_valid h hi)
  have hr : IsFormula language R := IsSemiformula.and.mpr ⟨hd,hg⟩
  apply source_implication_compose _ R _ native lo z (vectorInput_valid h) hr hd hc
  · intro native lo z _
    exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) _ _
      (NumericPAeqSupportedValueTotality.inputDomain_valid (substituted_environment h)).isUFormula hr.isUFormula false
  · intro native lo z _
    exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) _ _ hd.isUFormula hg.isUFormula true
theorem vector_substituted_totality {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t)
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (vectorInput s r b f a w) (valueTotalityCode b f (termSubst Presentation.language w t)))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (vectorInput s r b f a w) (valueTotalityCode b f (termSubst Presentation.language w t)))+1 := by
  have he := substituted_environment h
  apply source_implication_compose _ (inputDomain r b f) _ native lo z (vectorInput_valid h)
    (NumericPAeqSupportedValueTotality.inputDomain_valid he)
    (NumericPAeqSupportedValueTotality.valueTotality_isSemiformula he.1 he.2.1 he.2.2.1 he.2.2.2) hc
  · intro native lo z _
    exact vector_input_domain h (RelationalSource.Numeric.parameters 0 native lo z)
  · intro native lo z hc
    exact NumericPAeqSupportedValueTotality.guarded_value_totality_certificate he native lo z hc
theorem vector_original_totality {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t)
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (vectorInput s r b f a w) (valueTotalityCode a f t))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (vectorInput s r b f a w) (valueTotalityCode a f t))+1 := by
  have he := original_environment h
  apply source_implication_compose _ (inputDomain s a f) _ native lo z (vectorInput_valid h)
    (NumericPAeqSupportedValueTotality.inputDomain_valid he)
    (NumericPAeqSupportedValueTotality.valueTotality_isSemiformula he.1 he.2.1 he.2.2.1 he.2.2.2) hc
  · intro native lo z hc; exact vector_input_original_domain h native lo z hc
  · intro native lo z hc
    exact NumericPAeqSupportedValueTotality.guarded_value_totality_certificate he native lo z hc
#print axioms vector_input_original_domain
#print axioms vector_substituted_totality
#print axioms vector_original_totality
end M6.PA.NumericPAeqSupportedVectorRealization
