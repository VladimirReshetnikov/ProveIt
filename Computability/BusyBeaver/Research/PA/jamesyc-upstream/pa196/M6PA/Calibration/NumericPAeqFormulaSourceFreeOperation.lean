module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceFreeCalibration
public import M6PA.Calibration.NumericPAeqFormulaRecursion
@[expose] public section

/-! Last-bound source formula opening uses the existing changing-parameter
formula recursor; the threshold increases under each source quantifier. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (sourceFree sourceFreeVec)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def sourceFreeVecGraph : 𝚺ᴬ₁.Semisentence 4 :=
  (NumericPAeqTerm.SourceFree.blueprint.resultVec Presentation.language).rew <| Rew.subst ![#0,#2,#3,#1]
instance sourceFreeVec_defined : 𝚺ᴬ₁-Function₃ (sourceFreeVec : V→V→V→V) via sourceFreeVecGraph :=
  .mk fun v => by
    simpa [sourceFreeVecGraph,sourceFreeVec,Matrix.constant_eq_singleton,Matrix.comp_vecCons']
      using (NumericPAeqTerm.SourceFree.construction.resultVec_defined (L:=Presentation.language)).defined ![v 0,v 2,v 3,v 1]
namespace Opening
noncomputable def relGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out s k r ts. ∃ vs, !sourceFreeVecGraph vs s k ts ∧ !qqRelDef out k r vs”
noncomputable def nrelGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out s k r ts. ∃ vs, !sourceFreeVecGraph vs s k ts ∧ !qqNRelDef out k r vs”
noncomputable def allGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out s p ys. ∃ a, !nthDef a ys 0 ∧ !qqAllDef out a”
noncomputable def exsGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out s p ys. ∃ a, !nthDef a ys 0 ∧ !qqExsDef out a”
noncomputable def changeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma “out s i. out=s+1”
noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := relGraph
  nrel := nrelGraph
  verum := truthTranslationGraph
  falsum := falseTranslationGraph
  and := andTranslationGraph
  or := orTranslationGraph
  all := allGraph
  exs := exsGraph
  allChanges := changeGraph
  exsChanges := changeGraph
noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel := fun s k r ts => qqRel k r (sourceFreeVec s k ts)
  nrel := fun s k r ts => qqNRel k r (sourceFreeVec s k ts)
  verum := fun _ => qqVerum
  falsum := fun _ => qqFalsum
  and := fun _ _ _ a b => qqAnd a b
  or := fun _ _ _ a b => qqOr a b
  all := fun _ _ ys => qqAll (nth ys 0)
  exs := fun _ _ ys => qqExs (nth ys 0)
  allChanges := fun s _ => s+1
  exsChanges := fun s _ => s+1
  rel_defined := .mk fun v => by simp [blueprint,relGraph,Matrix.comp_vecCons'']
  nrel_defined := .mk fun v => by simp [blueprint,nrelGraph,Matrix.comp_vecCons'']
  verum_defined := .mk fun v => by simp [blueprint,truthTranslationGraph]
  falsum_defined := .mk fun v => by simp [blueprint,falseTranslationGraph]
  and_defined := .mk fun v => by simp [blueprint,andTranslationGraph]
  or_defined := .mk fun v => by simp [blueprint,orTranslationGraph]
  all_defined := .mk fun v => by simp [blueprint,allGraph,Matrix.comp_vecCons'']
  exs_defined := .mk fun v => by simp [blueprint,exsGraph,Matrix.comp_vecCons'']
  allChanges_defined := .mk fun v => by simp [blueprint,changeGraph]
  exChanges_defined := .mk fun v => by simp [blueprint,changeGraph]
  allChanges_monotone := fun _ => le_rfl
  exsChanges_monotone := fun _ => le_rfl
end Opening

noncomputable def formulaSourceFree (s p : V) : V := Opening.construction.result Presentation.language s p
noncomputable def formulaSourceFreeGraph : 𝚺ᴬ₁.Semisentence 3 := Opening.blueprint.result Presentation.language
instance formulaSourceFree_defined : 𝚺ᴬ₁-Function₂ (formulaSourceFree : V→V→V) via formulaSourceFreeGraph :=
  Opening.construction.result_defined (L:=Presentation.language)
theorem formulaSourceFree_graph (out s p : V) : formulaSourceFreeGraph.val.Evalb ![out,s,p] ↔ out=formulaSourceFree s p :=
  formulaSourceFree_defined.defined ![out,s,p]
instance formulaSourceFree_definable : 𝚺ᴬ₁-Function₂ (formulaSourceFree : V→V→V) := formulaSourceFree_defined.to_definable
instance formulaSourceFree_definable' (Γ m) : Γᴬ_[m+1]-Function₂ (formulaSourceFree : V→V→V) := formulaSourceFree_definable.of_sigmaOne

theorem formulaSourceFree_rel (s k r ts : V) (hr : Presentation.language.IsRel k r)
    (ht : IsUTermVec Presentation.language k ts) :
    formulaSourceFree s (qqRel k r ts)=qqRel k r (sourceFreeVec s k ts) :=
  Opening.construction.result_rel (L:=Presentation.language) hr ht
theorem formulaSourceFree_nrel (s k r ts : V) (hr : Presentation.language.IsRel k r)
    (ht : IsUTermVec Presentation.language k ts) :
    formulaSourceFree s (qqNRel k r ts)=qqNRel k r (sourceFreeVec s k ts) :=
  Opening.construction.result_nrel (L:=Presentation.language) hr ht
@[simp] theorem formulaSourceFree_verum (s : V) : formulaSourceFree s qqVerum=qqVerum :=
  Opening.construction.result_verum (L:=Presentation.language)
@[simp] theorem formulaSourceFree_falsum (s : V) : formulaSourceFree s qqFalsum=qqFalsum :=
  Opening.construction.result_falsum (L:=Presentation.language)
theorem formulaSourceFree_and (s p q : V) (hp : IsUFormula Presentation.language p) (hq : IsUFormula Presentation.language q) :
    formulaSourceFree s (qqAnd p q)=qqAnd (formulaSourceFree s p) (formulaSourceFree s q) :=
  Opening.construction.result_and (L:=Presentation.language) hp hq
theorem formulaSourceFree_or (s p q : V) (hp : IsUFormula Presentation.language p) (hq : IsUFormula Presentation.language q) :
    formulaSourceFree s (qqOr p q)=qqOr (formulaSourceFree s p) (formulaSourceFree s q) :=
  Opening.construction.result_or (L:=Presentation.language) hp hq
theorem formulaSourceFree_all (s p : V) (hp : IsUFormula Presentation.language p) :
    formulaSourceFree s (qqAll p)=qqAll (formulaSourceFree (s+1) p) := by
  simpa [formulaSourceFree,Opening.construction] using Opening.construction.result_all (L:=Presentation.language) (param:=s) hp rfl
theorem formulaSourceFree_exs (s p : V) (hp : IsUFormula Presentation.language p) :
    formulaSourceFree s (qqExs p)=qqExs (formulaSourceFree (s+1) p) := by
  simpa [formulaSourceFree,Opening.construction] using Opening.construction.result_exs (L:=Presentation.language) (param:=s) hp rfl

#print axioms sourceFreeVec_defined
#print axioms formulaSourceFree_defined
#print axioms formulaSourceFree_graph
#print axioms formulaSourceFree_rel
#print axioms formulaSourceFree_nrel
#print axioms formulaSourceFree_and
#print axioms formulaSourceFree_or
#print axioms formulaSourceFree_all
#print axioms formulaSourceFree_exs
end M6.PA.NumericPAeqFormula

