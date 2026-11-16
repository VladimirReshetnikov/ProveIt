module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueCoherenceShape
public import M6PA.Calibration.NumericPAeqSupportedValueTotalityBinaryShape
public import M6PA.Calibration.NumericPAeqBinaryCoherenceCode
@[expose] public section
namespace M6.PA.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence
open NumericPAeqSupportedValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem valuePredicate_addition {s b f u v:V}
    (hu:SupportedValueEnvironment s b f u) (hv:SupportedValueEnvironment s b f v):
    valuePredicate b f (qqFunc 2 2 (u∷(v∷0)))=
      binaryOutputCode additionTemplate (valuePredicate b f u) (valuePredicate b f v) := by
  unfold valuePredicate binaryOutputCode
  rw [valueSyntax_addition _ _ _ hu.2.2.1.isUTerm hv.2.2.1.isUTerm]
  simp only [parameters_result,additionValue]
  rw [NumericPAeqSupportedValueTotality.binary_child_instance hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 (by simp),
    NumericPAeqSupportedValueTotality.binary_child_instance hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 (by simp)]
theorem valuePredicate_multiplication {s b f u v:V}
    (hu:SupportedValueEnvironment s b f u) (hv:SupportedValueEnvironment s b f v):
    valuePredicate b f (qqFunc 2 3 (u∷(v∷0)))=
      binaryOutputCode multiplicationTemplate (valuePredicate b f u) (valuePredicate b f v) := by
  unfold valuePredicate binaryOutputCode
  rw [valueSyntax_multiplication _ _ _ hu.2.2.1.isUTerm hv.2.2.1.isUTerm]
  simp only [parameters_result,multiplicationValue]
  rw [NumericPAeqSupportedValueTotality.binary_child_instance hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 (by simp),
    NumericPAeqSupportedValueTotality.binary_child_instance hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 (by simp)]
#print axioms valuePredicate_addition
#print axioms valuePredicate_multiplication
end M6.PA.NumericPAeqSupportedValueCoherence
