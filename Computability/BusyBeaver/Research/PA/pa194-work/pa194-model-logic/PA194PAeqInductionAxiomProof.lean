import PA194PAeqOrdinaryTheoryClass
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def closedInductionProof (p : V) : V :=
  axm (insert (closedInduction p) (0 : V)) (closedInduction p)
noncomputable def closedInductionProofGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ q s, !closedInductionGraph q p ∧ !insertDef s q 0 ∧ !axmGraph out s q”
theorem closedInductionProof_graph (out p : V) :
    closedInductionProofGraph.val.Evalb ![out,p] ↔ out = closedInductionProof p := by
  simp [closedInductionProofGraph,closedInductionProof,Matrix.comp_vecCons'']
instance closedInductionProof_defined : 𝚺₁-Function₁ (closedInductionProof : V → V) via closedInductionProofGraph := .mk fun v => by
  change closedInductionProofGraph.val.Evalb v ↔ v 0 = closedInductionProof (v 1)
  have hv : ![v 0,v 1] = v := by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using closedInductionProof_graph (v 0) (v 1)

theorem closedInductionProof_valid {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    letI := ordinaryPAeq_delta
    Proof ordinaryPAeq (closedInductionProof p) (closedInduction p) := by
  letI := ordinaryPAeq_delta
  have hformula := (closedInduction_sentence hp).1
  have hclass : closedInduction p ∈ ordinaryPAeq.Δ₁Class :=
    (ordinaryPAeq_class _).mpr (Or.inr ⟨p,hp,rfl⟩)
  have hz : IsFormulaSet PA194PAeq.language (0 : V) := by
    change IsFormulaSet PA194PAeq.language (∅ : V)
    exact IsFormulaSet.empty
  have hs : IsFormulaSet PA194PAeq.language (insert (closedInduction p) (0 : V)) :=
    IsFormulaSet.insert_iff.mpr ⟨hformula,hz⟩
  have hmember : closedInduction p ∈ insert (closedInduction p) (0 : V) := by simp
  have hd : Derivation ordinaryPAeq (closedInductionProof p) := Derivation.axm hs hmember hclass
  refine ⟨?_,hd⟩
  simp [closedInductionProof,← emptyset_def]
#print axioms closedInductionProof_graph
#print axioms closedInductionProof_valid
end generic
end PA194PAeqBind
