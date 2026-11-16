import PA194TranslatedAxiomRule
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
variable (T : Theory SourceL) [T.Δ₁]
noncomputable def contextAxiomDerivation (param p target : V) : V :=
  axL target (translateFormula param p)
noncomputable def contextAxiomDerivationGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out param p target. ∃ q, !translateFormulaGraph q param p ∧ !axLGraph out target q”
theorem contextAxiomDerivation_graph (out param p target : V) :
    contextAxiomDerivationGraph.val.Evalb ![out,param,p,target] ↔ out = contextAxiomDerivation param p target := by
  simp [contextAxiomDerivationGraph,contextAxiomDerivation,translateFormula_graph,Matrix.comp_vecCons'']
instance contextAxiomDerivation_defined : 𝚺₁-Function₃ (contextAxiomDerivation : V → V → V → V) via contextAxiomDerivationGraph := .mk fun v => by
  change contextAxiomDerivationGraph.val.Evalb v ↔ v 0 = contextAxiomDerivation (v 1) (v 2) (v 3)
  have hv : ![v 0,v 1,v 2,v 3] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using contextAxiomDerivation_graph (v 0) (v 1) (v 2) (v 3)

theorem contextAxiomDerivation_valid {param p target : V}
    (hscope : IsSemiformula PA194PAeq.language 0 p) (hparam : ParametersValid 0 0 param)
    (hlen : p < len (nth param 1)) (hnlen : neg PA194PAeq.language p < len (nth param 1))
    (htarget : IsFormulaSet SourceL target)
    (hp : translateFormula param p ∈ target)
    (hnp : translateFormula param (neg PA194PAeq.language p) ∈ target) :
    Derivation T (contextAxiomDerivation param p target) := by
  have heq := translateFormula_neg hscope.isUFormula 0 0 param hscope hparam hlen hnlen
  apply Derivation.axL (T := T) htarget hp
  simpa [heq] using hnp

theorem contextAxiomDerivation_sequent (param p target : V) :
    fstIdx (contextAxiomDerivation param p target) = target := by
  simp [contextAxiomDerivation]
#print axioms contextAxiomDerivation_graph
#print axioms contextAxiomDerivation_valid
#print axioms contextAxiomDerivation_sequent
end generic
end PA194FormulaDispatcher
