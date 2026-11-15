import PA194PAeqFreeBoundBind
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def atomFreeBound (ar v : V) : V := listMax (termFreeBoundVec ar v)
noncomputable def atomFreeBoundGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out ar v. ∃ w, !termFreeBoundVecGraph w ar v ∧ !listMaxDef out w”
theorem atomFreeBound_graph (out ar v : V) : atomFreeBoundGraph.val.Evalb ![out,ar,v] ↔ out = atomFreeBound ar v := by
  simp [atomFreeBoundGraph,atomFreeBound,Matrix.comp_vecCons'']
instance atomFreeBound_defined : 𝚺₁-Function₂ (atomFreeBound : V → V → V) via atomFreeBoundGraph := .mk fun v => by
  change atomFreeBoundGraph.val.Evalb v ↔ v 0 = atomFreeBound (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using atomFreeBound_graph (v 0) (v 1) (v 2)
noncomputable def freeFormulaBlueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “out k ar r v. !atomFreeBoundGraph out ar v”
  nrel := .mkSigma “out k ar r v. !atomFreeBoundGraph out ar v”
  verum := .mkSigma “out k. out = 0”
  falsum := .mkSigma “out k. out = 0”
  and := .mkSigma “out k p q a b. !max.dfn out a b”
  or := .mkSigma “out k p q a b. !max.dfn out a b”
  all := .mkSigma “out k p child. out = child”
  exs := .mkSigma “out k p child. out = child”
  allChanges := .mkSigma “out k. out = k”
  exsChanges := .mkSigma “out k. out = k”
noncomputable def freeFormulaConstruction : UformulaRec1.Construction V freeFormulaBlueprint where
  rel _ ar _ v := atomFreeBound ar v
  nrel _ ar _ v := atomFreeBound ar v
  verum _ := 0
  falsum _ := 0
  and _ _ _ a b := max a b
  or _ _ _ a b := max a b
  all _ _ child := child
  exs _ _ child := child
  allChanges k := k
  exsChanges k := k
  rel_defined := .mk fun v => by simp [freeFormulaBlueprint]
  nrel_defined := .mk fun v => by simp [freeFormulaBlueprint]
  verum_defined := .mk fun v => by simp [freeFormulaBlueprint]
  falsum_defined := .mk fun v => by simp [freeFormulaBlueprint]
  and_defined := .mk fun v => by simp [freeFormulaBlueprint]
  or_defined := .mk fun v => by simp [freeFormulaBlueprint]
  all_defined := .mk fun v => by simp [freeFormulaBlueprint]
  exs_defined := .mk fun v => by simp [freeFormulaBlueprint]
  allChanges_defined := .mk fun v => by simp [freeFormulaBlueprint]
  exChanges_defined := .mk fun v => by simp [freeFormulaBlueprint]
noncomputable def formulaFreeBound (p : V) : V := freeFormulaConstruction.result PA194PAeq.language 0 p
noncomputable def formulaFreeBoundGraph : 𝚺₁.Semisentence 2 :=
  (freeFormulaBlueprint.result PA194PAeq.language).rew (Rew.subst ![#0,‘0’,#1])
instance formulaFreeBound_defined : 𝚺₁-Function₁ (formulaFreeBound : V → V) via formulaFreeBoundGraph := .mk fun v => by
  simp [formulaFreeBoundGraph,formulaFreeBound,Semiformula.eval_substs,freeFormulaConstruction.result_defined.df,Matrix.comp_vecCons'']
@[simp] theorem formulaFreeBound_rel {ar r v : V} (hr : PA194PAeq.language.IsRel ar r) (hv : IsUTermVec PA194PAeq.language ar v) :
    formulaFreeBound (^rel ar r v) = atomFreeBound ar v := by simp [formulaFreeBound,freeFormulaConstruction,hr,hv]
@[simp] theorem formulaFreeBound_nrel {ar r v : V} (hr : PA194PAeq.language.IsRel ar r) (hv : IsUTermVec PA194PAeq.language ar v) :
    formulaFreeBound (^nrel ar r v) = atomFreeBound ar v := by simp [formulaFreeBound,freeFormulaConstruction,hr,hv]
@[simp] theorem formulaFreeBound_verum : formulaFreeBound (^⊤ : V) = 0 := by simp [formulaFreeBound,freeFormulaConstruction]
@[simp] theorem formulaFreeBound_falsum : formulaFreeBound (^⊥ : V) = 0 := by simp [formulaFreeBound,freeFormulaConstruction]
@[simp] theorem formulaFreeBound_and {p q : V} (hp : IsUFormula PA194PAeq.language p) (hq : IsUFormula PA194PAeq.language q) :
    formulaFreeBound (p ^⋏ q) = max (formulaFreeBound p) (formulaFreeBound q) := by simp [formulaFreeBound,freeFormulaConstruction,hp,hq]
@[simp] theorem formulaFreeBound_or {p q : V} (hp : IsUFormula PA194PAeq.language p) (hq : IsUFormula PA194PAeq.language q) :
    formulaFreeBound (p ^⋎ q) = max (formulaFreeBound p) (formulaFreeBound q) := by simp [formulaFreeBound,freeFormulaConstruction,hp,hq]
@[simp] theorem formulaFreeBound_all {p : V} (hp : IsUFormula PA194PAeq.language p) :
    formulaFreeBound (^∀ p) = formulaFreeBound p := by simp [formulaFreeBound,freeFormulaConstruction,hp]
@[simp] theorem formulaFreeBound_exs {p : V} (hp : IsUFormula PA194PAeq.language p) :
    formulaFreeBound (^∃ p) = formulaFreeBound p := by simp [formulaFreeBound,freeFormulaConstruction,hp]
#print axioms formulaFreeBound_defined
#print axioms formulaFreeBound_rel
#print axioms formulaFreeBound_all
end generic
end PA194PAeqBind
