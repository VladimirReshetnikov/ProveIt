import PA194FormulaScope
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- A sufficient finite free environment for any source code p, filled with a fixed source free variable. -/
noncomputable def rootParameters (p : V) : V :=
  parameters 0 (repeatVec (^&(0 : V)) (p+1)) (^&(0 : V))
noncomputable def rootParametersGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ z free, !qqFvarDef z 0 ∧ !repeatVecDef free z (p+1) ∧ !parametersGraph out 0 free z”
theorem rootParameters_graph (out p : V) :
    rootParametersGraph.val.Evalb ![out,p] ↔ out = rootParameters p := by
  simp [rootParametersGraph,rootParameters,parameters_graph,Matrix.comp_vecCons'']
instance rootParameters_defined : 𝚺₁-Function₁ (rootParameters : V → V) via rootParametersGraph := .mk fun v => by
  change rootParametersGraph.val.Evalb v ↔ v 0 = rootParameters (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using rootParameters_graph (v 0) (v 1)

theorem rootParameters_valid (p : V) : ParametersValid 0 0 (rootParameters p) := by
  have hfree : IsSemitermVec SourceL (p+1) 0 (repeatVec (^&(0 : V)) (p+1)) := by
    constructor
    · constructor
      · simp
      · intro i hi
        rw [nth_repeatVec _ _ hi]
        simp
    · intro i hi
      rw [nth_repeatVec _ _ hi]
      simp
  unfold ParametersValid rootParameters
  simp only [parameters_bound,parameters_free,parameters_result]
  refine ⟨by simp,?_,by simp⟩
  simpa using hfree

theorem rootParameters_length (p : V) : p < len (nth (rootParameters p) 1) := by
  simp [rootParameters]
noncomputable def rootFormula (p : V) : V := translateFormula (rootParameters p) p
noncomputable def rootFormulaGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ param, !rootParametersGraph param p ∧ !translateFormulaGraph out param p”
theorem rootFormula_graph (out p : V) : rootFormulaGraph.val.Evalb ![out,p] ↔ out = rootFormula p := by
  simp [rootFormulaGraph,rootFormula,rootParameters_graph,translateFormula_graph,Matrix.comp_vecCons'']
instance rootFormula_defined : 𝚺₁-Function₁ (rootFormula : V → V) via rootFormulaGraph := .mk fun v => by
  change rootFormulaGraph.val.Evalb v ↔ v 0 = rootFormula (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using rootFormula_graph (v 0) (v 1)
theorem rootFormula_valid {p : V} (hp : IsSemiformula PA194PAeq.language 0 p) :
    IsSemiformula SourceL 0 (rootFormula p) :=
  formula_scope_translate hp.isUFormula 0 0 (rootParameters p) hp (rootParameters_valid p) (rootParameters_length p)
theorem rootFormula_falsum : rootFormula (^⊥ : V) = ^⊥ := translate_falsum _
#print axioms rootParameters_valid
#print axioms rootFormula_graph
#print axioms rootFormula_valid
#print axioms rootFormula_falsum
end generic
end PA194FormulaDispatcher
