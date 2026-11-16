import PA194PAeqInductionCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def closedInduction (p : V) : V := fullyClose (inductionBody p)
noncomputable def closedInductionGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ b, !inductionBodyGraph b p ∧ !fullyCloseGraph out b”
theorem closedInduction_graph (out p : V) :
    closedInductionGraph.val.Evalb ![out,p] ↔ out = closedInduction p := by
  simp [closedInductionGraph,closedInduction,Matrix.comp_vecCons'']
instance closedInduction_defined : 𝚺₁-Function₁ (closedInduction : V → V) via closedInductionGraph := .mk fun v => by
  change closedInductionGraph.val.Evalb v ↔ v 0 = closedInduction (v 1)
  have hv : ![v 0,v 1] = v := by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using closedInduction_graph (v 0) (v 1)
theorem closedInduction_sentence {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    IsSemiformula PA194PAeq.language 0 (closedInduction p) ∧
      shift PA194PAeq.language (closedInduction p) = closedInduction p :=
  fullyClose_sentence (inductionBody_scope hp)
theorem closedInduction_quote (p : Semiproposition PA194PAeq.language 1) :
    closedInduction (⌜p⌝ : V) = (⌜(PA194PAeq.inductionFormula p).univCl⌝ : V) := by
  rw [closedInduction,inductionBody_quote,fullyClose_quote]
#print axioms closedInduction_graph
#print axioms closedInduction_sentence
#print axioms closedInduction_quote
end generic
end PA194PAeqBind
