import PA194PAeqOrdinalParameters
import PA194PAeqLanguage
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqTermFormulaTree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194PAeqOrdinalValues
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Dummy relational atoms distinguish the two term-variable kinds. -/
noncomputable def boundLeaf (i : V) : V := ^rel (2 : V) 0 (?[ ^#i, ^#i] : V)
noncomputable def freeLeaf (i : V) : V := ^nrel (2 : V) 0 (?[ ^&i, ^&i] : V)
noncomputable def boundLeafGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out i. ∃ a tail v, !qqBvarDef a i ∧ !adjoinDef tail a 0 ∧ !adjoinDef v a tail ∧ !qqRelDef out 2 0 v”
noncomputable def freeLeafGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out i. ∃ a tail v, !qqFvarDef a i ∧ !adjoinDef tail a 0 ∧ !adjoinDef v a tail ∧ !qqNRelDef out 2 0 v”
theorem boundLeaf_graph (out i : V) : boundLeafGraph.val.Evalb ![out,i] ↔ out = boundLeaf i := by
  simp [boundLeafGraph,boundLeaf]
theorem freeLeaf_graph (out i : V) : freeLeafGraph.val.Evalb ![out,i] ↔ out = freeLeaf i := by
  simp [freeLeafGraph,freeLeaf]
instance boundLeaf_defined : 𝚺₁-Function₁ (boundLeaf : V → V) via boundLeafGraph := .mk fun v => by
  change boundLeafGraph.val.Evalb v ↔ v 0 = boundLeaf (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using boundLeaf_graph (v 0) (v 1)
instance freeLeaf_defined : 𝚺₁-Function₁ (freeLeaf : V → V) via freeLeafGraph := .mk fun v => by
  change freeLeafGraph.val.Evalb v ↔ v 0 = freeLeaf (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using freeLeaf_graph (v 0) (v 1)

/-- Binder nodes mark the parameter changes needed by the two binary children. -/
noncomputable def leftMarker (p : V) : V := ^∀ (^∃ p)
noncomputable def rightMarker (p : V) : V := ^∀ (^∀ p)
noncomputable def functionNode (k f w : V) : V :=
  if k = 0 then ^⊤ else if k = 1 then ^⊤ ^⋏ (^∀ (w.[0])) else
    if f = 2 then leftMarker (w.[0]) ^⋏ rightMarker (w.[1])
    else leftMarker (w.[0]) ^⋎ rightMarker (w.[1])
noncomputable def functionNodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out k f w.
    (k=0 ∧ !qqVerumDef out) ∨
    (k≠0 ∧ k=1 ∧ ∃ u a top, !nthDef u w 0 ∧ !qqAllDef a u ∧ !qqVerumDef top ∧ !qqAndDef out top a) ∨
    (k≠0 ∧ k≠1 ∧ f=2 ∧ ∃ u v u1 u2 v1 v2,
      !nthDef u w 0 ∧ !nthDef v w 1 ∧ !qqExsDef u1 u ∧ !qqAllDef u2 u1 ∧
      !qqAllDef v1 v ∧ !qqAllDef v2 v1 ∧ !qqAndDef out u2 v2) ∨
    (k≠0 ∧ k≠1 ∧ f≠2 ∧ ∃ u v u1 u2 v1 v2,
      !nthDef u w 0 ∧ !nthDef v w 1 ∧ !qqExsDef u1 u ∧ !qqAllDef u2 u1 ∧
      !qqAllDef v1 v ∧ !qqAllDef v2 v1 ∧ !qqOrDef out u2 v2)”
theorem functionNode_graph (out k f w : V) :
    functionNodeGraph.val.Evalb ![out,k,f,w] ↔ out = functionNode k f w := by
  by_cases hk0 : k=0 <;> by_cases hk1 : k=1 <;> by_cases hf : f=2 <;>
    simp [functionNodeGraph,functionNode,leftMarker,rightMarker,hk0,hk1,hf]
instance functionNode_defined : 𝚺₁-Function₃ (functionNode : V → V → V → V) via functionNodeGraph := .mk fun v => by
  change functionNodeGraph.val.Evalb v ↔ v 0 = functionNode (v 1) (v 2) (v 3)
  have hv : ![v 0,v 1,v 2,v 3] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using functionNode_graph (v 0) (v 1) (v 2) (v 3)

noncomputable def treeBlueprint : Language.TermRec.Blueprint 0 where
  bvar := boundLeafGraph
  fvar := freeLeafGraph
  func := .mkSigma “out k f v w. !functionNodeGraph out k f w”
noncomputable def treeConstruction : Language.TermRec.Construction V treeBlueprint where
  bvar _ i := boundLeaf i
  fvar _ i := freeLeaf i
  func _ k f _ w := functionNode k f w
  bvar_defined := .mk fun v => by simpa [treeBlueprint] using boundLeaf_defined.defined v
  fvar_defined := .mk fun v => by simpa [treeBlueprint] using freeLeaf_defined.defined v
  func_defined := .mk fun v => by
    simp only [treeBlueprint,HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [functionNode_defined.df]

noncomputable def termTree (t : V) : V := treeConstruction.result PA194PAeq.language ![] t
noncomputable def termTreeVec (k ts : V) : V := treeConstruction.resultVec PA194PAeq.language ![] k ts
noncomputable def termTreeGraph : 𝚺₁.Semisentence 2 := treeBlueprint.result PA194PAeq.language
instance termTree_defined : 𝚺₁-Function₁ (termTree : V → V) via termTreeGraph := .mk fun v => by
  have hempty : (fun _ : Fin 0 => v 1) = (![] : Fin 0 → V) := Subsingleton.elim _ _
  simpa [termTreeGraph,termTree,hempty] using treeConstruction.result_defined.defined v
@[simp] theorem termTree_bvar (i : V) : termTree (^#i) = boundLeaf i := by
  simp [termTree,treeConstruction]
@[simp] theorem termTree_fvar (i : V) : termTree (^&i) = freeLeaf i := by
  simp [termTree,treeConstruction]
theorem termTree_func {k f ts : V} (hf : PA194PAeq.language.IsFunc k f)
    (ht : IsUTermVec PA194PAeq.language k ts) :
    termTree (^func k f ts) = functionNode k f (termTreeVec k ts) := by
  simp [termTree,termTreeVec,treeConstruction,hf,ht]
@[simp] theorem termTreeVec_nth {k ts i : V} (ht : IsUTermVec PA194PAeq.language k ts) (hi : i<k) :
    nth (termTreeVec k ts) i = termTree (nth ts i) :=
  treeConstruction.nth_resultVec PA194PAeq.language ![] ht hi

/-- A valid PAeq term yields a valid tagged relational formula tree. -/
theorem termTree_valid (t : V) (ht : IsUTerm PA194PAeq.language t) :
    IsUFormula SourceL (termTree t) := by
  haveI : 𝚺₁-Function₁ (termTree : V → V) := termTree_defined.to_definable
  have hdef : 𝚺₁-Predicate (fun x : V => IsUFormula SourceL (termTree x)) := by definability
  have hr : SourceL.IsRel (2 : V) (0 : V) := by
    change (“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : V), 0]
    simp
  apply IsUTerm.induction 𝚺 hdef ?_ ?_ ?_ t ht
  · intro z
    simp [boundLeaf,IsUFormula.rel,hr]
  · intro z
    simp [freeLeaf,IsUFormula.nrel,hr]
  · intro k f v hf hv ih
    rw [termTree_func hf hv]
    have hc : ∀ i < k, IsUFormula SourceL ((termTreeVec k v).[i]) := by
      intro i hi
      rw [termTreeVec_nth hv hi]
      exact ih i hi
    rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,hf⟩
    · simp [functionNode,IsUFormula.verum]
    · have h0 := hc 0 (by simp)
      simp [functionNode,IsUFormula.and,IsUFormula.all,h0]
    · have h0 := hc 0 (by simp)
      have h1 := hc 1 (by simp)
      by_cases h2 : f = 2
      · simp [functionNode,leftMarker,rightMarker,IsUFormula.and,IsUFormula.all,IsUFormula.ex,h0,h1,h2]
      · simp [functionNode,leftMarker,rightMarker,IsUFormula.or,IsUFormula.all,IsUFormula.ex,h0,h1,h2]

#print axioms termTree_valid
#print axioms termTree_defined
#print axioms termTree_bvar
#print axioms termTree_fvar
#print axioms termTree_func
#print axioms termTreeVec_nth
end generic
end PA194PAeqTermFormulaTree
