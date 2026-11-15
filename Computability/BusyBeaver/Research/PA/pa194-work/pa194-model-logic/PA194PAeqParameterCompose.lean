import PA194PAeqOrdinalParameters
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqOrdinalValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Shift once under a binder, selecting an arbitrary bound result slot. -/
noncomputable def shiftParameters (param i : V) : V :=
  parameters (shiftTerms (nth param 0)) (shiftTerms (nth param 1)) (^#i)
noncomputable def shiftParametersGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out param i. ∃ b f bs fs z,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !shiftTermsGraph bs b ∧ !shiftTermsGraph fs f ∧
    !qqBvarDef z i ∧ !parametersGraph out bs fs z”
theorem shiftParameters_graph (out param i : V) :
    shiftParametersGraph.val.Evalb ![out,param,i] ↔ out = shiftParameters param i := by
  simp [shiftParametersGraph,shiftParameters,shiftTerms_graph,parameters_graph,Matrix.comp_vecCons'']
instance shiftParameters_defined : 𝚺₁-Function₂ (shiftParameters : V → V → V) via shiftParametersGraph := .mk fun v => by
  change shiftParametersGraph.val.Evalb v ↔ v 0 = shiftParameters (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using shiftParameters_graph (v 0) (v 1) (v 2)

theorem shiftParameters_valid {s n param i : V} (h : ParametersValid s n param) (hi : i < n+1) :
    ParametersValid s (n+1) (shiftParameters param i) := by
  rcases h with ⟨hb,hf,hz⟩
  unfold ParametersValid shiftParameters
  simp only [parameters_bound,parameters_free,parameters_result]
  refine ⟨shiftTerms_valid hb,?_,?_⟩
  · simpa [shiftTerms_length hf] using shiftTerms_valid hf
  · simpa [IsSemiterm.bvar] using hi

theorem shiftParameters_zero (param : V) : shiftParameters param 0 = childParameters param := rfl

theorem shiftParameters_child (param i : V) :
    shiftParameters (childParameters param) i = binaryParameters param i := by
  simp [shiftParameters,childParameters,binaryParameters]

#print axioms shiftParameters_graph
#print axioms shiftParameters_valid
#print axioms shiftParameters_child
end generic
end PA194PAeqOrdinalValues
