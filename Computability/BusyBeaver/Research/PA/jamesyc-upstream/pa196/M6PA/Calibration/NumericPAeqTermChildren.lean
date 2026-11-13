module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermBinaryConstructors
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The result index is 1 for the left child, 0 for the right child. -/
noncomputable def binaryParameters (param i : V) : V := parameters
  (shiftTerms (shiftTerms (nth param 0))) (shiftTerms (shiftTerms (nth param 1))) (qqBvar i)
noncomputable def binaryParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param i. ∃ b f b1 f1 b2 f2 z,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !shiftTermsGraph b1 b ∧ !shiftTermsGraph f1 f ∧
    !shiftTermsGraph b2 b1 ∧ !shiftTermsGraph f2 f1 ∧ !qqBvarDef z i ∧ !parametersGraph out b2 f2 z”
theorem binaryParameters_graph (out param i : V) :
    binaryParametersGraph.val.Evalb ![out,param,i] ↔ out=binaryParameters param i := by
  simp [binaryParametersGraph,binaryParameters,parameters_graph,shiftTerms_graph,Matrix.comp_vecCons'']
instance binaryParameters_defined : 𝚺ᴬ₁-Function₂ (binaryParameters : V → V → V) via binaryParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! binaryParameters_graph (v 0) (v 1) (v 2)
theorem binaryParameters_total_unique (param i : V) :
    ∃! out, binaryParametersGraph.val.Evalb ![out,param,i] := by
  refine ⟨binaryParameters param i,(binaryParameters_graph _ _ _).mpr rfl,?_⟩
  intro out h; exact (binaryParameters_graph _ _ _).mp h

theorem binaryParameters_valid {s n param i : V} (h : ParametersValid s n param) (hi : i<2) :
    ParametersValid s ((n+1)+1) (binaryParameters param i) := by
  rcases h with ⟨hb,hf,hz⟩
  have hb1 := shiftTerms_isSemitermVec hb
  have hf1 := shiftTerms_isSemitermVec hf
  unfold ParametersValid binaryParameters
  simp only [parameters_bound,parameters_free,parameters_result]
  refine ⟨shiftTerms_isSemitermVec hb1,?_,?_⟩
  · simpa [shiftTerms_length hf1] using shiftTerms_isSemitermVec hf1
  · simp only [IsSemiterm.bvar]
    exact lt_of_lt_of_le hi (calc
      (2:V) = 1+1 := one_add_one_eq_two.symm
      _ ≤ (n+1)+1 := add_le_add (by simp) le_rfl)

theorem binaryParameters_bound_nth {s n param i j : V}
    (h : ParametersValid s n param) (hj : j<s) :
    nth (nth (binaryParameters param i) 0) j=
      termBShift language (termBShift language (nth (nth param 0) j)) := by
  simp only [binaryParameters,parameters_bound]
  rw [shiftTerms_nth (shiftTerms_isSemitermVec h.1) hj,shiftTerms_nth h.1 hj]

theorem unary_child_rank (u : V) : u<qqFunc 1 1 (u∷0) :=
  lt_trans (by simp) (terms_lt_qqFunc 1 1 (u∷0))
theorem binary_left_rank (f u v : V) : u<qqFunc 2 f (u∷(v∷0)) :=
  lt_trans (by simp) (terms_lt_qqFunc 2 f (u∷(v∷0)))
theorem binary_right_rank (f u v : V) : v<qqFunc 2 f (u∷(v∷0)) :=
  lt_trans (show v < (u∷(v∷0)) from lt_trans (show v<(v∷0) by simp) (by simp))
    (terms_lt_qqFunc 2 f (u∷(v∷0)))

#print axioms binaryParameters_graph
#print axioms binaryParameters_defined
#print axioms binaryParameters_total_unique
#print axioms binaryParameters_valid
#print axioms binaryParameters_bound_nth
#print axioms unary_child_rank
#print axioms binary_left_rank
#print axioms binary_right_rank
end M6.PA.NumericPAeqTerm

