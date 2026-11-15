import PA194PAeqTermFormulaTree
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def bindFree (k i : V) : V := if i=0 then ^#k else ^&(i-1)
noncomputable def bindFreeGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out k i. (i=0 ∧ !qqBvarDef out k) ∨ (i≠0 ∧ ∃ j, !subDef j i 1 ∧ !qqFvarDef out j)”
theorem bindFree_graph (out k i : V) : bindFreeGraph.val.Evalb ![out,k,i] ↔ out = bindFree k i := by
  by_cases h : i=0 <;> simp [bindFreeGraph,bindFree,h]
instance bindFree_defined : 𝚺₁-Function₂ (bindFree : V → V → V) via bindFreeGraph := .mk fun v => by
  change bindFreeGraph.val.Evalb v ↔ v 0 = bindFree (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using bindFree_graph (v 0) (v 1) (v 2)

noncomputable def termBlueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “out i k. !qqBvarDef out i”
  fvar := .mkSigma “out i k. !bindFreeGraph out k i”
  func := .mkSigma “out ar f v w k. !qqFuncDef out ar f w”
noncomputable def termConstruction : Language.TermRec.Construction V termBlueprint where
  bvar _ i := ^#i
  fvar params i := bindFree (params 0) i
  func _ ar f _ w := ^func ar f w
  bvar_defined := .mk fun v => by simp [termBlueprint]
  fvar_defined := .mk fun v => by simp [termBlueprint,bindFree_graph,Matrix.comp_vecCons'']
  func_defined := .mk fun v => by simp [termBlueprint]
noncomputable def bindTerm (k t : V) : V := termConstruction.result PA194PAeq.language ![k] t
noncomputable def bindTermVec (k ar v : V) : V := termConstruction.resultVec PA194PAeq.language ![k] ar v
noncomputable def bindTermGraph : 𝚺₁.Semisentence 3 :=
  (termBlueprint.result PA194PAeq.language).rew (Rew.subst ![#0,#2,#1])
instance bindTerm_defined : 𝚺₁-Function₂ (bindTerm : V → V → V) via bindTermGraph := .mk fun v => by
  change bindTermGraph.val.Evalb v ↔ v 0 = bindTerm (v 1) (v 2)
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
  simp [bindTermGraph,bindTerm,Semiformula.eval_substs,termConstruction.result_defined.df,Matrix.comp_vecCons'',hk]
@[simp] theorem bindTerm_bvar (k i : V) : bindTerm k (^#i) = ^#i := by simp [bindTerm,termConstruction]
@[simp] theorem bindTerm_fvar (k i : V) : bindTerm k (^&i) = bindFree k i := by simp [bindTerm,termConstruction]
theorem bindTerm_func {k ar f v : V} (hf : PA194PAeq.language.IsFunc ar f)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    bindTerm k (^func ar f v) = ^func ar f (bindTermVec k ar v) := by
  simp [bindTerm,bindTermVec,termConstruction,hf,hv]
theorem bindTermVec_nth {k ar v i : V} (hv : IsUTermVec PA194PAeq.language ar v) (hi : i<ar) :
    nth (bindTermVec k ar v) i = bindTerm k (nth v i) :=
  termConstruction.nth_resultVec PA194PAeq.language ![k] hv hi
#print axioms bindTerm_defined
#print axioms bindTerm_bvar
#print axioms bindTerm_fvar
#print axioms bindTerm_func
#print axioms bindTermVec_nth
end generic
end PA194PAeqBind
