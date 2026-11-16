import PA194PAeqUnbindTermInverse
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def unbindTermVecGraph : 𝚺₁.Semisentence 4 :=
  (unbindTermBlueprint.resultVec PA194PAeq.language).rew (Rew.subst ![#0,#2,#3,#1])
instance unbindTermVec_defined : 𝚺₁-Function₃ (unbindTermVec : V → V → V → V) via unbindTermVecGraph := .mk fun v => by
  change unbindTermVecGraph.val.Evalb v ↔ v 0 = unbindTermVec (v 1) (v 2) (v 3)
  have hk : (fun _ : Fin 1 => v 1) = (![v 1] : Fin 1 → V) := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp [unbindTermVecGraph,unbindTermVec,Semiformula.eval_substs,unbindTermConstruction.resultVec_defined.df,Matrix.comp_vecCons'',hk]
noncomputable def unbindFormulaBlueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “out depth k r v. ∃ w, !unbindTermVecGraph w depth k v ∧ !qqRelDef out k r w”
  nrel := .mkSigma “out depth k r v. ∃ w, !unbindTermVecGraph w depth k v ∧ !qqNRelDef out k r w”
  verum := .mkSigma “out depth. !qqVerumDef out”
  falsum := .mkSigma “out depth. !qqFalsumDef out”
  and := .mkSigma “out depth p q l r. !qqAndDef out l r”
  or := .mkSigma “out depth p q l r. !qqOrDef out l r”
  all := .mkSigma “out depth p child. !qqAllDef out child”
  exs := .mkSigma “out depth p child. !qqExsDef out child”
  allChanges := .mkSigma “out depth. out = depth+1”
  exsChanges := .mkSigma “out depth. out = depth+1”
noncomputable def unbindFormulaConstruction : UformulaRec1.Construction V unbindFormulaBlueprint where
  rel depth k r v := ^rel k r (unbindTermVec depth k v)
  nrel depth k r v := ^nrel k r (unbindTermVec depth k v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ l r := l ^⋏ r
  or _ _ _ l r := l ^⋎ r
  all _ _ child := ^∀ child
  exs _ _ child := ^∃ child
  allChanges depth := depth+1
  exsChanges depth := depth+1
  rel_defined := .mk fun v => by simp [unbindFormulaBlueprint,Matrix.comp_vecCons'']
  nrel_defined := .mk fun v => by simp [unbindFormulaBlueprint,Matrix.comp_vecCons'']
  verum_defined := .mk fun v => by simp [unbindFormulaBlueprint]
  falsum_defined := .mk fun v => by simp [unbindFormulaBlueprint]
  and_defined := .mk fun v => by simp [unbindFormulaBlueprint]
  or_defined := .mk fun v => by simp [unbindFormulaBlueprint]
  all_defined := .mk fun v => by simp [unbindFormulaBlueprint]
  exs_defined := .mk fun v => by simp [unbindFormulaBlueprint]
  allChanges_defined := .mk fun v => by simp [unbindFormulaBlueprint]
  exChanges_defined := .mk fun v => by simp [unbindFormulaBlueprint]
noncomputable def unbindFormula (k p : V) : V := unbindFormulaConstruction.result PA194PAeq.language k p
noncomputable def unbindFormulaGraph : 𝚺₁.Semisentence 3 := unbindFormulaBlueprint.result PA194PAeq.language
instance unbindFormula_defined : 𝚺₁-Function₂ (unbindFormula : V → V → V) via unbindFormulaGraph := .mk fun v => by
  change unbindFormulaGraph.val.Evalb v ↔ v 0 = unbindFormula (v 1) (v 2)
  simpa [unbindFormulaGraph,unbindFormula] using unbindFormulaConstruction.result_defined.defined v
@[simp] theorem unbindFormula_rel {k ar r v : V} (hr : PA194PAeq.language.IsRel ar r)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    unbindFormula k (^rel ar r v) = ^rel ar r (unbindTermVec k ar v) := by simp [unbindFormula,unbindFormulaConstruction,hr,hv]
@[simp] theorem unbindFormula_nrel {k ar r v : V} (hr : PA194PAeq.language.IsRel ar r)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    unbindFormula k (^nrel ar r v) = ^nrel ar r (unbindTermVec k ar v) := by simp [unbindFormula,unbindFormulaConstruction,hr,hv]
@[simp] theorem unbindFormula_verum (k : V) : unbindFormula k ^⊤ = ^⊤ := by simp [unbindFormula,unbindFormulaConstruction]
@[simp] theorem unbindFormula_falsum (k : V) : unbindFormula k ^⊥ = ^⊥ := by simp [unbindFormula,unbindFormulaConstruction]
@[simp] theorem unbindFormula_and {k p q : V} (hp : IsUFormula PA194PAeq.language p) (hq : IsUFormula PA194PAeq.language q) :
    unbindFormula k (p ^⋏ q) = unbindFormula k p ^⋏ unbindFormula k q := by simp [unbindFormula,unbindFormulaConstruction,hp,hq]
@[simp] theorem unbindFormula_or {k p q : V} (hp : IsUFormula PA194PAeq.language p) (hq : IsUFormula PA194PAeq.language q) :
    unbindFormula k (p ^⋎ q) = unbindFormula k p ^⋎ unbindFormula k q := by simp [unbindFormula,unbindFormulaConstruction,hp,hq]
@[simp] theorem unbindFormula_all {k p : V} (hp : IsUFormula PA194PAeq.language p) :
    unbindFormula k (^∀ p) = ^∀ (unbindFormula (k+1) p) := by simp [unbindFormula,unbindFormulaConstruction,hp]
@[simp] theorem unbindFormula_exs {k p : V} (hp : IsUFormula PA194PAeq.language p) :
    unbindFormula k (^∃ p) = ^∃ (unbindFormula (k+1) p) := by simp [unbindFormula,unbindFormulaConstruction,hp]
#print axioms unbindTermVec_defined
#print axioms unbindFormula_defined
#print axioms unbindFormula_rel
#print axioms unbindFormula_all
end generic
end PA194PAeqBind
