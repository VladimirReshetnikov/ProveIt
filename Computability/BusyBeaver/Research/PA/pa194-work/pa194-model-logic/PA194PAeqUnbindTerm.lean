import PA194PAeqClosedInduction
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def unbindBound (k i : V) : V := if i<k then ^#i else ^&(0 : V)
noncomputable def unbindBoundGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out k i. (i<k ∧ !qqBvarDef out i) ∨ (i≥k ∧ !qqFvarDef out 0)”
theorem unbindBound_graph (out k i : V) : unbindBoundGraph.val.Evalb ![out,k,i] ↔ out = unbindBound k i := by
  by_cases h : i<k
  · simp [unbindBoundGraph,unbindBound,h]
  · simp [unbindBoundGraph,unbindBound,h,le_of_not_gt h]
instance unbindBound_defined : 𝚺₁-Function₂ (unbindBound : V → V → V) via unbindBoundGraph := .mk fun v => by
  change unbindBoundGraph.val.Evalb v ↔ v 0 = unbindBound (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using unbindBound_graph (v 0) (v 1) (v 2)

noncomputable def unbindTermBlueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “out i k. !unbindBoundGraph out k i”
  fvar := .mkSigma “out i k. ∃ j, j=i+1 ∧ !qqFvarDef out j”
  func := .mkSigma “out ar f v w k. !qqFuncDef out ar f w”
noncomputable def unbindTermConstruction : Language.TermRec.Construction V unbindTermBlueprint where
  bvar params i := unbindBound (params 0) i
  fvar _ i := ^&(i+1)
  func _ ar f _ w := ^func ar f w
  bvar_defined := .mk fun v => by simp [unbindTermBlueprint,Matrix.comp_vecCons'']
  fvar_defined := .mk fun v => by simp [unbindTermBlueprint]
  func_defined := .mk fun v => by simp [unbindTermBlueprint]
noncomputable def unbindTerm (k t : V) : V := unbindTermConstruction.result PA194PAeq.language ![k] t
noncomputable def unbindTermVec (k ar v : V) : V := unbindTermConstruction.resultVec PA194PAeq.language ![k] ar v
noncomputable def unbindTermGraph : 𝚺₁.Semisentence 3 :=
  (unbindTermBlueprint.result PA194PAeq.language).rew (Rew.subst ![#0,#2,#1])
instance unbindTerm_defined : 𝚺₁-Function₂ (unbindTerm : V → V → V) via unbindTermGraph := .mk fun v => by
  change unbindTermGraph.val.Evalb v ↔ v 0 = unbindTerm (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  have hk : (fun _ : Fin 1 => v 1) = (![v 1] : Fin 1 → V) := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp [unbindTermGraph,unbindTerm,Semiformula.eval_substs,unbindTermConstruction.result_defined.df,Matrix.comp_vecCons'',hk]
@[simp] theorem unbindTerm_bvar (k i : V) : unbindTerm k (^#i) = unbindBound k i := by simp [unbindTerm,unbindTermConstruction]
@[simp] theorem unbindTerm_fvar (k i : V) : unbindTerm k (^&i) = ^&(i+1) := by simp [unbindTerm,unbindTermConstruction]
theorem unbindTerm_func {k ar f v : V} (hf : PA194PAeq.language.IsFunc ar f)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    unbindTerm k (^func ar f v) = ^func ar f (unbindTermVec k ar v) := by
  simp [unbindTerm,unbindTermVec,unbindTermConstruction,hf,hv]
theorem unbindTermVec_nth {k ar v i : V} (hv : IsUTermVec PA194PAeq.language ar v) (hi : i<ar) :
    nth (unbindTermVec k ar v) i = unbindTerm k (nth v i) :=
  unbindTermConstruction.nth_resultVec PA194PAeq.language ![k] hv hi
#print axioms unbindTerm_defined
#print axioms unbindTerm_bvar
#print axioms unbindTerm_fvar
#print axioms unbindTerm_func
#print axioms unbindTermVec_nth
end generic
end PA194PAeqBind
