module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueTotalitySyntax
public import M6PA.Calibration.NumericPAeqValueCoherenceSyntax
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section

/-! Genuine free-support coverage for existing paired value comparison syntax.
No source-code size bound or replacement of the target syntax. -/
namespace M6.PA.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence
open NumericPAeqSupportedValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def SupportedCoherenceEnvironment (s b c f g t:V) : Prop :=
  SupportedValueEnvironment s b f t ∧ SupportedValueEnvironment s c g t
private theorem value_at_two {s b f t i:V} (h:SupportedValueEnvironment s b f t) (hi:i<2) :
    IsSemiformula language 2 (valueSyntax (parameters b f (qqBvar i)) t) := by
  have hb : IsSemitermVec language s 2 b := by
    have h' := shiftTerms_isSemitermVec (shiftTerms_isSemitermVec h.1)
    simpa [shiftTerms_zero_arity h.1,zero_add,one_add_one_eq_two] using h'
  have hf : IsSemitermVec language (len f) 2 f := by
    have h' := shiftTerms_isSemitermVec (shiftTerms_isSemitermVec h.2.1)
    simpa [shiftTerms_zero_arity h.2.1,zero_add,one_add_one_eq_two] using h'
  apply valueSyntax_supported_isSemiformula
  refine ⟨?_,h.2.2.1,?_⟩
  · simpa [ParametersValid] using And.intro hb (And.intro hf (show IsSemiterm language 2 (qqBvar i) from IsSemiterm.bvar.mpr hi))
  · simpa using h.2.2.2

theorem comparisonCode_valid {s b c f g t:V} (h:SupportedCoherenceEnvironment s b c f g t) :
    IsFormula language (comparisonCode b c f g t) := by
  apply IsSemiformula.all.mpr
  apply IsSemiformula.all.mpr
  apply IsSemiformula.imp.mpr
  constructor
  · apply IsSemiformula.and.mpr
    constructor
    · simpa [zero_add,one_add_one_eq_two] using value_at_two h.1 (show (1:V)<2 by simp)
    · simpa [zero_add,one_add_one_eq_two] using value_at_two h.2 (show (0:V)<2 by simp)
  · apply NumericPAeqValueIsoGuard.isoCode_isSemiformula <;> simp

theorem coherenceInput_valid {s b c f g t:V} (h:SupportedCoherenceEnvironment s b c f g t) :
    IsFormula language (coherenceInput s b c f g) := by
  apply IsSemiformula.and.mpr
  refine ⟨NumericPAeqSupportedValueTotality.inputDomain_valid h.1,IsSemiformula.and.mpr ⟨NumericPAeqSupportedValueTotality.inputDomain_valid h.2,?_⟩⟩
  apply IsSemiformula.and.mpr
  refine ⟨NumericPAeqValueIsoGuard.guard_vector_isSemiformula h.1.1 h.2.1,?_⟩
  apply NumericPAeqValueIsoGuard.guard_isSemiformula
  intro i hi
  exact ⟨h.1.2.1.nth (lt_of_lt_of_le hi (min_le_left _ _)),h.2.2.1.nth (lt_of_lt_of_le hi (min_le_right _ _))⟩

theorem coherenceCode_valid {s b c f g t:V} (h:SupportedCoherenceEnvironment s b c f g t) :
    IsFormula language (coherenceCode s b c f g t) :=
  IsSemiformula.imp.mpr ⟨coherenceInput_valid h,comparisonCode_valid h⟩

#print axioms comparisonCode_valid
#print axioms coherenceInput_valid
#print axioms coherenceCode_valid
end M6.PA.NumericPAeqSupportedValueCoherence

