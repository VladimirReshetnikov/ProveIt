import PA194FormulaNegation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]

noncomputable def translatedAxiomSequent (param p : V) : V :=
  insert (translateFormula param p) (insert (translateFormula param (neg PA194PAeq.language p)) (0 : V))
noncomputable def translatedAxiomDerivation (param p : V) : V :=
  axL (translatedAxiomSequent param p) (translateFormula param p)

theorem translatedAxiom_valid {param p : V}
    (hscope : IsSemiformula PA194PAeq.language 0 p) (hparam : ParametersValid 0 0 param)
    (hlen : p < len (nth param 1)) (hnlen : neg PA194PAeq.language p < len (nth param 1)) :
    Derivation T (translatedAxiomDerivation param p) := by
  have hp := formula_scope_translate hscope.isUFormula 0 0 param hscope hparam hlen
  have hneg := translateFormula_neg hscope.isUFormula 0 0 param hscope hparam hlen hnlen
  have hn : IsSemiformula SourceL 0 (translateFormula param (neg PA194PAeq.language p)) := by
    rw [hneg]
    exact hp.neg
  apply Derivation.axL (T := T)
  · simp [translatedAxiomDerivation,translatedAxiomSequent,hp,hn,← emptyset_def]
  · simp [translatedAxiomDerivation,translatedAxiomSequent]
  · simp [translatedAxiomDerivation,translatedAxiomSequent,hneg]

theorem translatedAxiom_sequent (param p : V) :
    fstIdx (translatedAxiomDerivation param p) = translatedAxiomSequent param p := by
  simp [translatedAxiomDerivation]

noncomputable def translatedAxiomSequentGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out param p. ∃ q np nq tail, !translateFormulaGraph q param p ∧
    !(negGraph PA194PAeq.language) np p ∧ !translateFormulaGraph nq param np ∧
    !insertDef tail nq 0 ∧ !insertDef out q tail”
theorem translatedAxiomSequent_graph (out param p : V) :
    translatedAxiomSequentGraph.val.Evalb ![out,param,p] ↔ out = translatedAxiomSequent param p := by
  simp [translatedAxiomSequentGraph,translatedAxiomSequent,translateFormula_graph,Matrix.comp_vecCons'']
instance translatedAxiomSequent_defined : 𝚺₁-Function₂ (translatedAxiomSequent : V → V → V) via translatedAxiomSequentGraph := .mk fun v => by
  change translatedAxiomSequentGraph.val.Evalb v ↔ v 0 = translatedAxiomSequent (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using translatedAxiomSequent_graph (v 0) (v 1) (v 2)
noncomputable def translatedAxiomDerivationGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out param p. ∃ q seq, !translateFormulaGraph q param p ∧ !translatedAxiomSequentGraph seq param p ∧ !axLGraph out seq q”
theorem translatedAxiomDerivation_graph (out param p : V) :
    translatedAxiomDerivationGraph.val.Evalb ![out,param,p] ↔ out = translatedAxiomDerivation param p := by
  simp [translatedAxiomDerivationGraph,translatedAxiomDerivation,translateFormula_graph,translatedAxiomSequent_graph,Matrix.comp_vecCons'']
instance translatedAxiomDerivation_defined : 𝚺₁-Function₂ (translatedAxiomDerivation : V → V → V) via translatedAxiomDerivationGraph := .mk fun v => by
  change translatedAxiomDerivationGraph.val.Evalb v ↔ v 0 = translatedAxiomDerivation (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using translatedAxiomDerivation_graph (v 0) (v 1) (v 2)
#print axioms translatedAxiom_valid
#print axioms translatedAxiom_sequent
#print axioms translatedAxiomDerivation_graph
#print axioms translatedAxiomDerivation_defined
end generic
end PA194FormulaDispatcher
