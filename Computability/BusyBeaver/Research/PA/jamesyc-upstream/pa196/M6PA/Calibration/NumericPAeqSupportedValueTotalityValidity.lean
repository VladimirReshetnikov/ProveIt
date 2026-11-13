module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueTotalitySyntax
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section
namespace M6.PA.NumericPAeqSupportedValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem valueTotality_isSemiformula {s n b f t : V}
    (hb:IsSemitermVec language s n b) (hf:IsSemitermVec language (len f) n f)
    (ht:IsSemiterm Presentation.language s t) (hbound:FreeSupported (len f) t) :
    IsSemiformula language n (valueTotalityCode b f t) := by
  apply IsSemiformula.exs.mpr
  apply valueSyntax_supported_isSemiformula
  refine ⟨?_,ht,?_⟩
  · simp only [ParametersValid,parameters_bound,parameters_free,parameters_result]
    refine ⟨shiftTerms_isSemitermVec hb,?_,by simp⟩
    rw [shiftTerms_length hf]
    exact shiftTerms_isSemitermVec hf
  · simpa only [parameters_free,shiftTerms_length hf] using hbound

theorem guardedTotality_valid {s b f t : V} (h:SupportedValueEnvironment s b f t) :
    IsFormula language (guardedTotalityCode s b f t) :=
  IsSemiformula.imp.mpr ⟨inputDomain_valid h,valueTotality_isSemiformula h.1 h.2.1 h.2.2.1 h.2.2.2⟩
#print axioms valueTotality_isSemiformula
#print axioms guardedTotality_valid
end M6.PA.NumericPAeqSupportedValueTotality

