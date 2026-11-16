module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaParameters
@[expose] public section

/-! The exact two existential value environments for arithmetic equality.
Both source environments shift twice; result indices one and zero are distinct
actual bound variables. These are syntax parameters, not ordinal values. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqTerm (shiftTerms shiftTermsGraph shiftTerms_graph shiftTerms_isSemitermVec
  shiftTerms_length shiftTerms_nth)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def equalityTermParameters (param index : V) : V :=
  NumericPAeqTerm.parameters (shiftTerms (shiftTerms (nth param 0)))
    (shiftTerms (shiftTerms (nth param 1))) (qqBvar index)
noncomputable def equalityTermParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param index. ∃ b f bs fs bss fss result,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !shiftTermsGraph bs b ∧ !shiftTermsGraph fs f ∧
    !shiftTermsGraph bss bs ∧ !shiftTermsGraph fss fs ∧ !qqBvarDef result index ∧
    !NumericPAeqTerm.parametersGraph out bss fss result”
theorem equalityTermParameters_graph (out param index : V) :
    equalityTermParametersGraph.val.Evalb ![out,param,index] ↔ out=equalityTermParameters param index := by
  simp [equalityTermParametersGraph,equalityTermParameters,NumericPAeqTerm.parameters_graph,
    Matrix.comp_vecCons'']
instance equalityTermParameters_defined :
    𝚺ᴬ₁-Function₂ (equalityTermParameters : V → V → V) via equalityTermParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! equalityTermParameters_graph (v 0) (v 1) (v 2)
theorem equalityTermParameters_total_unique (param index : V) :
    ∃! out,equalityTermParametersGraph.val.Evalb ![out,param,index] :=
  ⟨equalityTermParameters param index,(equalityTermParameters_graph _ _ _).mpr rfl,
    fun _ h => (equalityTermParameters_graph _ _ _).mp h⟩

theorem equalityTermParameters_valid {s n param index : V}
    (h : ParametersValid s n param) (hi : index<2) :
    NumericPAeqTerm.ParametersValid s (n+1+1) (equalityTermParameters param index) := by
  unfold NumericPAeqTerm.ParametersValid equalityTermParameters
  simp only [NumericPAeqTerm.parameters_bound,NumericPAeqTerm.parameters_free,NumericPAeqTerm.parameters_result]
  refine ⟨shiftTerms_isSemitermVec (shiftTerms_isSemitermVec h.1),?_,?_⟩
  · simpa [shiftTerms_length (shiftTerms_isSemitermVec h.2),shiftTerms_length h.2]
      using shiftTerms_isSemitermVec (shiftTerms_isSemitermVec h.2)
  · have hn : (2:V)≤n+1+1 := by simp [add_assoc,one_add_one_eq_two]
    simpa using lt_of_lt_of_le hi hn

theorem equalityTermParameters_bound_nth {s n param index i : V}
    (h : ParametersValid s n param) (hi : i<s) :
    nth (nth (equalityTermParameters param index) 0) i=
      termBShift language (termBShift language (nth (nth param 0) i)) := by
  simp only [equalityTermParameters,NumericPAeqTerm.parameters_bound]
  rw [shiftTerms_nth (shiftTerms_isSemitermVec h.1) hi,shiftTerms_nth h.1 hi]

theorem equalityTermParameters_free_nth {s n param index i : V}
    (h : ParametersValid s n param) (hi : i<len (nth param 1)) :
    nth (nth (equalityTermParameters param index) 1) i=
      termBShift language (termBShift language (nth (nth param 1) i)) := by
  simp only [equalityTermParameters,NumericPAeqTerm.parameters_free]
  rw [shiftTerms_nth (shiftTerms_isSemitermVec h.2) hi,shiftTerms_nth h.2 hi]

@[simp] theorem equalityTermParameters_result (param index : V) :
    nth (equalityTermParameters param index) 2=qqBvar index := by simp [equalityTermParameters]

#print axioms equalityTermParameters_defined
#print axioms equalityTermParameters_total_unique
#print axioms equalityTermParameters_valid
#print axioms equalityTermParameters_bound_nth
#print axioms equalityTermParameters_free_nth
#print axioms equalityTermParameters_result
end M6.PA.NumericPAeqFormula

