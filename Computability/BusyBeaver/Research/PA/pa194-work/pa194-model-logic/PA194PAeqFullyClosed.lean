import PA194PAeqTypedFormulaBound
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def fullyClose (p : V) : V := close (formulaFreeBound p) p
noncomputable def fullyCloseGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ n, !formulaFreeBoundGraph n p ∧ !closeGraph out n p”
theorem fullyClose_graph (out p : V) : fullyCloseGraph.val.Evalb ![out,p] ↔ out = fullyClose p := by
  simp [fullyCloseGraph,fullyClose,Matrix.comp_vecCons'']
instance fullyClose_defined : 𝚺₁-Function₁ (fullyClose : V → V) via fullyCloseGraph := .mk fun v => by
  change fullyCloseGraph.val.Evalb v ↔ v 0 = fullyClose (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using fullyClose_graph (v 0) (v 1)
theorem fullyClose_sentence {p : V} (hp : IsSemiformula PA194PAeq.language 0 p) :
    IsSemiformula PA194PAeq.language 0 (fullyClose p) ∧ shift PA194PAeq.language (fullyClose p) = fullyClose p :=
  close_closed _ hp (le_refl _)
theorem fullyClose_quote (p : Proposition PA194PAeq.language) :
    fullyClose (⌜p⌝ : V) = (⌜p.univCl⌝ : V) := by
  rw [fullyClose,formulaFreeBound_quote_fvSup,close_quote_univCl]
#print axioms fullyClose_graph
#print axioms fullyClose_sentence
#print axioms fullyClose_quote
end generic
end PA194PAeqBind
