import PA194PAeqBindTermScope
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def bindTermVecGraph : 𝚺₁.Semisentence 4 :=
  (termBlueprint.resultVec PA194PAeq.language).rew (Rew.subst ![#0,#2,#3,#1])
instance bindTermVec_defined : 𝚺₁-Function₃ (bindTermVec : V → V → V → V) via bindTermVecGraph := .mk fun v => by
  change bindTermVecGraph.val.Evalb v ↔ v 0 = bindTermVec (v 1) (v 2) (v 3)
  have hk : (fun _ : Fin 1 => v 1) = (![v 1] : Fin 1 → V) := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp [bindTermVecGraph,bindTermVec,Semiformula.eval_substs,termConstruction.resultVec_defined.df,Matrix.comp_vecCons'',hk]
noncomputable def formulaBlueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “out depth k r v. ∃ w, !bindTermVecGraph w depth k v ∧ !qqRelDef out k r w”
  nrel := .mkSigma “out depth k r v. ∃ w, !bindTermVecGraph w depth k v ∧ !qqNRelDef out k r w”
  verum := .mkSigma “out depth. !qqVerumDef out”
  falsum := .mkSigma “out depth. !qqFalsumDef out”
  and := .mkSigma “out depth p q l r. !qqAndDef out l r”
  or := .mkSigma “out depth p q l r. !qqOrDef out l r”
  all := .mkSigma “out depth p child. !qqAllDef out child”
  exs := .mkSigma “out depth p child. !qqExsDef out child”
  allChanges := .mkSigma “out depth. out = depth+1”
  exsChanges := .mkSigma “out depth. out = depth+1”
noncomputable def formulaConstruction : UformulaRec1.Construction V formulaBlueprint where
  rel depth k r v := ^rel k r (bindTermVec depth k v)
  nrel depth k r v := ^nrel k r (bindTermVec depth k v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ l r := l ^⋏ r
  or _ _ _ l r := l ^⋎ r
  all _ _ child := ^∀ child
  exs _ _ child := ^∃ child
  allChanges depth := depth+1
  exsChanges depth := depth+1
  rel_defined := .mk fun v => by simp [formulaBlueprint,Matrix.comp_vecCons'']
  nrel_defined := .mk fun v => by simp [formulaBlueprint,Matrix.comp_vecCons'']
  verum_defined := .mk fun v => by simp [formulaBlueprint]
  falsum_defined := .mk fun v => by simp [formulaBlueprint]
  and_defined := .mk fun v => by simp [formulaBlueprint]
  or_defined := .mk fun v => by simp [formulaBlueprint]
  all_defined := .mk fun v => by simp [formulaBlueprint]
  exs_defined := .mk fun v => by simp [formulaBlueprint]
  allChanges_defined := .mk fun v => by simp [formulaBlueprint]
  exChanges_defined := .mk fun v => by simp [formulaBlueprint]
noncomputable def bindFormula (k p : V) : V := formulaConstruction.result PA194PAeq.language k p
noncomputable def bindFormulaGraph : 𝚺₁.Semisentence 3 := formulaBlueprint.result PA194PAeq.language
instance bindFormula_defined : 𝚺₁-Function₂ (bindFormula : V → V → V) via bindFormulaGraph := .mk fun v => by
  change bindFormulaGraph.val.Evalb v ↔ v 0 = bindFormula (v 1) (v 2)
  simpa [bindFormulaGraph,bindFormula] using formulaConstruction.result_defined.defined v
@[simp] theorem bindFormula_rel {k ar r v : V} (hr : PA194PAeq.language.IsRel ar r)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    bindFormula k (^rel ar r v) = ^rel ar r (bindTermVec k ar v) := by simp [bindFormula,formulaConstruction,hr,hv]
@[simp] theorem bindFormula_nrel {k ar r v : V} (hr : PA194PAeq.language.IsRel ar r)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    bindFormula k (^nrel ar r v) = ^nrel ar r (bindTermVec k ar v) := by simp [bindFormula,formulaConstruction,hr,hv]
@[simp] theorem bindFormula_verum (k : V) : bindFormula k ^⊤ = ^⊤ := by simp [bindFormula,formulaConstruction]
@[simp] theorem bindFormula_falsum (k : V) : bindFormula k ^⊥ = ^⊥ := by simp [bindFormula,formulaConstruction]
@[simp] theorem bindFormula_and {k p q : V} (hp : IsUFormula PA194PAeq.language p) (hq : IsUFormula PA194PAeq.language q) :
    bindFormula k (p ^⋏ q) = bindFormula k p ^⋏ bindFormula k q := by simp [bindFormula,formulaConstruction,hp,hq]
@[simp] theorem bindFormula_or {k p q : V} (hp : IsUFormula PA194PAeq.language p) (hq : IsUFormula PA194PAeq.language q) :
    bindFormula k (p ^⋎ q) = bindFormula k p ^⋎ bindFormula k q := by simp [bindFormula,formulaConstruction,hp,hq]
@[simp] theorem bindFormula_all {k p : V} (hp : IsUFormula PA194PAeq.language p) :
    bindFormula k (^∀ p) = ^∀ (bindFormula (k+1) p) := by simp [bindFormula,formulaConstruction,hp]
@[simp] theorem bindFormula_exs {k p : V} (hp : IsUFormula PA194PAeq.language p) :
    bindFormula k (^∃ p) = ^∃ (bindFormula (k+1) p) := by simp [bindFormula,formulaConstruction,hp]
#print axioms bindTermVec_defined
#print axioms bindFormula_defined
#print axioms bindFormula_rel
#print axioms bindFormula_all
end generic
end PA194PAeqBind
