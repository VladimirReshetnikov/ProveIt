module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueTotalityValidity
public import M6PA.Calibration.NumericPAeqTermSupportedBoundInstance
public import M6PA.Calibration.NumericPAeqValueBoundInstance
public import M6PA.Calibration.NumericPAeqValueSuccessorShape
@[expose] public section

/-! Exact independent left/right value predicates at binary result binders.
Neither child is identified with the other. -/
namespace M6.PA.NumericPAeqSupportedValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem binary_child_instance {s b f t i : V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (ht:IsSemiterm Presentation.language s t) (hbound:FreeSupported (len f) t) (hi:i<2) :
    valueSyntax (binaryParameters (parameters b f (qqBvar 0)) i) t=
      substs1 language (qqBvar i) (valueSyntax (parameters b f (qqBvar 0)) t) := by
  rw [valueSyntax_supported_bound_instance hb hf ht hbound (show IsSemiterm language 2 (qqBvar i) from IsSemiterm.bvar.mpr hi)]
  simp [binaryParameters,shiftTerms_zero_arity hb,shiftTerms_zero_arity hf]

theorem valueTotality_addition_shape {s b f u v : V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language s u) (hv:IsSemiterm Presentation.language s v)
    (hub:FreeSupported (len f) u) (hvb:FreeSupported (len f) v) :
    valueTotalityCode b f (qqFunc 2 2 (u∷(v∷0)))=
      qqExs (binaryValue additionTemplate (qqBvar 0)
        (substs1 language (qqBvar 1) (valueSyntax (parameters b f (qqBvar 0)) u))
        (substs1 language (qqBvar 0) (valueSyntax (parameters b f (qqBvar 0)) v))) := by
  rw [valueTotality_zero_environments hb hf,valueSyntax_addition _ _ _ hu.isUTerm hv.isUTerm]
  simp only [parameters_result,additionValue]
  rw [binary_child_instance hb hf hu hub (by simp),binary_child_instance hb hf hv hvb (by simp)]

theorem valueTotality_multiplication_shape {s b f u v : V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language s u) (hv:IsSemiterm Presentation.language s v)
    (hub:FreeSupported (len f) u) (hvb:FreeSupported (len f) v) :
    valueTotalityCode b f (qqFunc 2 3 (u∷(v∷0)))=
      qqExs (binaryValue multiplicationTemplate (qqBvar 0)
        (substs1 language (qqBvar 1) (valueSyntax (parameters b f (qqBvar 0)) u))
        (substs1 language (qqBvar 0) (valueSyntax (parameters b f (qqBvar 0)) v))) := by
  rw [valueTotality_zero_environments hb hf,valueSyntax_multiplication _ _ _ hu.isUTerm hv.isUTerm]
  simp only [parameters_result,multiplicationValue]
  rw [binary_child_instance hb hf hu hub (by simp),binary_child_instance hb hf hv hvb (by simp)]

#print axioms binary_child_instance
#print axioms valueTotality_addition_shape
#print axioms valueTotality_multiplication_shape
end M6.PA.NumericPAeqSupportedValueTotality

