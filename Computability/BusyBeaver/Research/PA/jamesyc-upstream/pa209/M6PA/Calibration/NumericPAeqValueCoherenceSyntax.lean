module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueGuardedTotalitySyntax
public import M6PA.Calibration.NumericPAeqValueClosedEnvironment
public import M6PA.Calibration.NumericPAeqValueIsoGuardValidity
@[expose] public section

/-! Paired finite environments and universal two-value comparison syntax.
Free vectors may have different lengths; only their common prefix is compared. -/
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def CoherenceEnvironment (s b c f g t:V) : Prop :=
  ValueEnvironment s b f t ∧ ValueEnvironment s c g t
noncomputable def comparisonCode (b c f g t:V) : V :=
  qqAll (qqAll (imp language
    (qqAnd (valueSyntax (parameters b f (qqBvar 1)) t) (valueSyntax (parameters c g (qqBvar 0)) t))
    (NumericPAeqValueIsoGuard.isoCode (qqBvar 1) (qqBvar 0))))
noncomputable def coherenceInput (s b c f g:V) : V :=
  qqAnd (inputDomain s b f) (qqAnd (inputDomain s c g)
    (qqAnd (NumericPAeqValueIsoGuard.guard b c s)
      (NumericPAeqValueIsoGuard.guard f g (min (len f) (len g)))))
noncomputable def coherenceCode (s b c f g t:V) : V :=
  imp language (coherenceInput s b c f g) (comparisonCode b c f g t)

private theorem value_at_two {s b f t i:V} (h:ValueEnvironment s b f t) (hi:i<2) :
    IsSemiformula language 2 (valueSyntax (parameters b f (qqBvar i)) t) := by
  have hb : IsSemitermVec language s 2 b := by
    have h' := shiftTerms_isSemitermVec (shiftTerms_isSemitermVec h.1)
    simpa [shiftTerms_zero_arity h.1,zero_add,one_add_one_eq_two] using h'
  have hf : IsSemitermVec language (len f) 2 f := by
    have h' := shiftTerms_isSemitermVec (shiftTerms_isSemitermVec h.2.1)
    simpa [shiftTerms_zero_arity h.2.1,zero_add,one_add_one_eq_two] using h'
  apply valueSyntax_isSemiformula
  refine ⟨?_,h.2.2.1,?_⟩
  · simpa [ParametersValid] using And.intro hb (And.intro hf (show IsSemiterm language 2 (qqBvar i) from IsSemiterm.bvar.mpr hi))
  · simpa using h.2.2.2

theorem comparisonCode_valid {s b c f g t:V} (h:CoherenceEnvironment s b c f g t) :
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

theorem coherenceInput_valid {s b c f g t:V} (h:CoherenceEnvironment s b c f g t) :
    IsFormula language (coherenceInput s b c f g) := by
  apply IsSemiformula.and.mpr
  refine ⟨inputDomain_valid h.1,IsSemiformula.and.mpr ⟨inputDomain_valid h.2,?_⟩⟩
  apply IsSemiformula.and.mpr
  refine ⟨NumericPAeqValueIsoGuard.guard_vector_isSemiformula h.1.1 h.2.1,?_⟩
  apply NumericPAeqValueIsoGuard.guard_isSemiformula
  intro i hi
  exact ⟨h.1.2.1.nth (lt_of_lt_of_le hi (min_le_left _ _)),h.2.2.1.nth (lt_of_lt_of_le hi (min_le_right _ _))⟩

theorem coherenceCode_valid {s b c f g t:V} (h:CoherenceEnvironment s b c f g t) :
    IsFormula language (coherenceCode s b c f g t) :=
  IsSemiformula.imp.mpr ⟨coherenceInput_valid h,comparisonCode_valid h⟩

#print axioms comparisonCode_valid
#print axioms coherenceInput_valid
#print axioms coherenceCode_valid
end M6.PA.NumericPAeqValueCoherence

