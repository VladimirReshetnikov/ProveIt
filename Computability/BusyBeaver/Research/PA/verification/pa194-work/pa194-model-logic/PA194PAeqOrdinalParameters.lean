import PA194PAeqOrdinalValues
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqOrdinalValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Shift all terms of a target environment under a new binder. -/
noncomputable def shiftTerms (v : V) : V := termBShiftVec SourceL (len v) v
noncomputable def shiftTermsGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out v. ∃ k, !lenDef k v ∧ !(termBShiftVecGraph SourceL) out k v”
theorem shiftTerms_graph (out v : V) :
    shiftTermsGraph.val.Evalb ![out,v] ↔ out = shiftTerms v := by
  simp [shiftTermsGraph,shiftTerms]
instance shiftTerms_defined : 𝚺₁-Function₁ (shiftTerms : V → V) via shiftTermsGraph := .mk fun v => by
  change shiftTermsGraph.val.Evalb v ↔ v 0 = shiftTerms (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using shiftTerms_graph (v 0) (v 1)

theorem shiftTerms_length {k n v : V} (h : IsSemitermVec SourceL k n v) :
    len (shiftTerms v) = k := by simp [shiftTerms,h.lh,h.isUTerm]
theorem shiftTerms_nth {k n v i : V} (h : IsSemitermVec SourceL k n v) (hi : i < k) :
    nth (shiftTerms v) i = termBShift SourceL (nth v i) := by
  simp [shiftTerms,h.lh,nth_termBShiftVec h.isUTerm hi]
theorem shiftTerms_valid {k n v : V} (h : IsSemitermVec SourceL k n v) :
    IsSemitermVec SourceL k (n+1) (shiftTerms v) := by
  simpa [shiftTerms,h.lh] using h.termBShiftVec

/-- A parameter packet holds bound/free term vectors and a result term. -/
noncomputable def parameters (b f z : V) : V := ?[b,f,z]
noncomputable def parametersGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out b f z. ∃ zs fs, !adjoinDef zs z 0 ∧ !adjoinDef fs f zs ∧ !adjoinDef out b fs”
theorem parameters_graph (out b f z : V) :
    parametersGraph.val.Evalb ![out,b,f,z] ↔ out = parameters b f z := by
  simp [parametersGraph,parameters]
instance parameters_defined : 𝚺₁-Function₃ (parameters : V → V → V → V) via parametersGraph := .mk fun v => by
  change parametersGraph.val.Evalb v ↔ v 0 = parameters (v 1) (v 2) (v 3)
  have hv : ![v 0,v 1,v 2,v 3] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using parameters_graph (v 0) (v 1) (v 2) (v 3)
@[simp] theorem parameters_bound (b f z : V) : nth (parameters b f z) 0 = b := by simp [parameters]
@[simp] theorem parameters_free (b f z : V) : nth (parameters b f z) 1 = f := by simp [parameters]
@[simp] theorem parameters_result (b f z : V) : nth (parameters b f z) 2 = z := by simp [parameters]

noncomputable def childParameters (param : V) : V :=
  parameters (shiftTerms (nth param 0)) (shiftTerms (nth param 1)) (^#(0 : V))
noncomputable def childParametersGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out param. ∃ b f bs fs z,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !shiftTermsGraph bs b ∧ !shiftTermsGraph fs f ∧
    !qqBvarDef z 0 ∧ !parametersGraph out bs fs z”
theorem childParameters_graph (out param : V) :
    childParametersGraph.val.Evalb ![out,param] ↔ out = childParameters param := by
  simp [childParametersGraph,childParameters,shiftTerms_graph,parameters_graph,Matrix.comp_vecCons'']

instance childParameters_defined : 𝚺₁-Function₁ (childParameters : V → V) via childParametersGraph := .mk fun v => by
  change childParametersGraph.val.Evalb v ↔ v 0 = childParameters (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using childParameters_graph (v 0) (v 1)

/-- The free vector may have a length independent of the source bound arity. -/
def ParametersValid (sourceArity targetArity param : V) : Prop :=
  IsSemitermVec SourceL sourceArity targetArity (nth param 0) ∧
  IsSemitermVec SourceL (len (nth param 1)) targetArity (nth param 1) ∧
  IsSemiterm SourceL targetArity (nth param 2)

theorem childParameters_valid {s n param : V} (h : ParametersValid s n param) :
    ParametersValid s (n+1) (childParameters param) := by
  rcases h with ⟨hb,hf,hz⟩
  unfold ParametersValid childParameters
  simp only [parameters_bound,parameters_free,parameters_result]
  refine ⟨shiftTerms_valid hb,?_,by simp⟩
  simpa [shiftTerms_length hf] using shiftTerms_valid hf

theorem childParameters_bound_nth {s n param i : V} (h : ParametersValid s n param) (hi : i<s) :
    nth (nth (childParameters param) 0) i = termBShift SourceL (nth (nth param 0) i) := by
  simpa [childParameters] using shiftTerms_nth h.1 hi

theorem childParameters_free_nth {s n param i : V} (h : ParametersValid s n param)
    (hi : i<len (nth param 1)) :
    nth (nth (childParameters param) 1) i = termBShift SourceL (nth (nth param 1) i) := by
  simpa [childParameters] using shiftTerms_nth h.2.1 hi

noncomputable def binaryParameters (param i : V) : V := parameters
  (shiftTerms (shiftTerms (nth param 0))) (shiftTerms (shiftTerms (nth param 1))) (^#i)
noncomputable def binaryParametersGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out param i. ∃ b f b1 f1 b2 f2 z,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !shiftTermsGraph b1 b ∧ !shiftTermsGraph f1 f ∧
    !shiftTermsGraph b2 b1 ∧ !shiftTermsGraph f2 f1 ∧ !qqBvarDef z i ∧ !parametersGraph out b2 f2 z”
theorem binaryParameters_graph (out param i : V) :
    binaryParametersGraph.val.Evalb ![out,param,i] ↔ out = binaryParameters param i := by
  simp [binaryParametersGraph,binaryParameters,parameters_graph,shiftTerms_graph,Matrix.comp_vecCons'']

instance binaryParameters_defined : 𝚺₁-Function₂ (binaryParameters : V → V → V) via binaryParametersGraph := .mk fun v => by
  change binaryParametersGraph.val.Evalb v ↔ v 0 = binaryParameters (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using binaryParameters_graph (v 0) (v 1) (v 2)

theorem binaryParameters_valid {s n param i : V} (h : ParametersValid s n param) (hi : i<2) :
    ParametersValid s ((n+1)+1) (binaryParameters param i) := by
  rcases h with ⟨hb,hf,hz⟩
  have hb1 := shiftTerms_valid hb
  have hf1 := shiftTerms_valid hf
  unfold ParametersValid binaryParameters
  simp only [parameters_bound,parameters_free,parameters_result]
  refine ⟨shiftTerms_valid hb1,?_,?_⟩
  · simpa [shiftTerms_length hf1] using shiftTerms_valid hf1
  · simp only [IsSemiterm.bvar]
    exact lt_of_lt_of_le hi (calc
      (2:V) = 1+1 := one_add_one_eq_two.symm
      _ ≤ (n+1)+1 := add_le_add (by simp) le_rfl)

#print axioms shiftTerms_graph
#print axioms shiftTerms_valid
#print axioms childParameters_graph
#print axioms childParameters_valid
#print axioms childParameters_bound_nth
#print axioms binaryParameters_graph
#print axioms binaryParameters_valid
end generic
end PA194PAeqOrdinalValues
