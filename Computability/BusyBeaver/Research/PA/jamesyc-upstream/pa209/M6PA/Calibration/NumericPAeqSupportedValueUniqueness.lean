module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueUniquenessInput
@[expose] public section
namespace M6.PA.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence ActualCheckerBlueprint
open NumericPAeqSupportedValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem guarded_value_uniqueness_certificate {s b f t:V} (h:SupportedValueEnvironment s b f t) (native lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (uniquenessCode s b f t)):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (uniquenessCode s b f t)+1 := by
  apply source_implication_compose _ (coherenceInput s b b f f) _ native lo z (NumericPAeqSupportedValueTotality.inputDomain_valid h)
    (coherenceInput_valid ⟨h,h⟩) (comparisonCode_valid ⟨h,h⟩) hc
  · intro native lo z hc; exact diagonal_input_certificate h native lo z hc
  · intro native lo z hc; exact guarded_value_coherence_certificate ⟨h,h⟩ native lo z hc
#print axioms guarded_value_uniqueness_certificate
end M6.PA.NumericPAeqSupportedValueCoherence
