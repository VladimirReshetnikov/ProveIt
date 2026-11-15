import PA194ModelClosureComplexity
import PA194ModelSepRootGraph
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def pureBindTerm (k t : V) : V :=
  if t = 0 then 0 else
  if pi₁ (t-1) = 1 then
    if pi₂ (t-1) = 0 then ^#k else ^&(pi₂ (t-1)-1)
  else t

theorem pureBindTermGraph_iff (y k t : V) :
    bindTermGraph.val.Eval ![y,k,t] Empty.elim ↔ y = pureBindTerm k t := by
  simp only [bindTermGraph]
  simp
  rcases zero_or_succ t with rfl | ⟨d,rfl⟩
  · simp [pureBindTerm]
  · have hpair : pair (pi₁ d) (pi₂ d) = d := by
      simpa only [pi₁,pi₂] using pair_unpair d
    simp only [pureBindTerm,add_ne_zero,Arithmetic.one_ne_zero,or_true,ite_false,add_tsub_cancel_right]
    constructor
    · rintro (h0 | ⟨r,a,ht,hcases⟩)
      · simp at h0
      · have hd : d = pair r a := add_right_cancel ht
        subst d
        simp only [pi₁_pair,pi₂_pair]
        rcases hcases with h | h | h
        · rcases h with ⟨rfl,rfl,hy⟩; simpa using hy
        · rcases h with ⟨rfl,x,hx,hy⟩; subst a; simpa using hy
        · rcases h with ⟨hr,hy⟩; simpa [hr] using hy
    · intro hy
      right
      refine ⟨pi₁ d,pi₂ d,?_,?_⟩
      · rw [hpair]
      · by_cases hr : pi₁ d = 1
        · by_cases hz : pi₂ d = 0
          · left; exact ⟨hr,hz,by simpa [hr,hz] using hy⟩
          · right; left
            obtain ⟨x,hx⟩ := (zero_or_succ (pi₂ d)).resolve_left hz
            refine ⟨hr,x,hx,?_⟩
            simpa [hr,hx] using hy
        · right; right; exact ⟨hr,by simpa [hr] using hy⟩

local instance pureBindTerm_defined : 𝚺₁-Function₂ (pureBindTerm : V → V → V) via bindTermGraph := .mk fun v ↦ by
  change bindTermGraph.val.Eval v Empty.elim ↔ v 0 = pureBindTerm (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using (pureBindTermGraph_iff (v 0) (v 1) (v 2))

noncomputable def pureBindPair (k v : V) : V := ?[pureBindTerm k v.[0], pureBindTerm k v.[1]]
theorem pureBindPairGraph_iff (y k v : V) :
    bindPairGraph.val.Eval ![y,k,v] Empty.elim ↔ y = pureBindPair k v := by
  simp [bindPairGraph, pureBindPair]

local instance pureBindPair_defined : 𝚺₁-Function₂ (pureBindPair : V → V → V) via bindPairGraph := .mk fun v ↦ by
  change bindPairGraph.val.Eval v Empty.elim ↔ v 0 = pureBindPair (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using (pureBindPairGraph_iff (v 0) (v 1) (v 2))

noncomputable def pureFormulaCloseConstruction : UformulaRec1.Construction V FormulaClose.blueprint where
  rel := fun depth k R v ↦ ^rel k R (pureBindPair depth v)
  nrel := fun depth k R v ↦ ^nrel k R (pureBindPair depth v)
  verum := fun _ ↦ ^⊤
  falsum := fun _ ↦ ^⊥
  and := fun _ _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or := fun _ _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all := fun _ _ y₁ ↦ ^∀ y₁
  exs := fun _ _ y₁ ↦ ^∃ y₁
  allChanges := fun depth ↦ depth+1
  exsChanges := fun depth ↦ depth+1
  rel_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  nrel_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  verum_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  falsum_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  and_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  or_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  all_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  exs_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  allChanges_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]
  exChanges_defined := .mk fun v ↦ by simp [FormulaClose.blueprint]

noncomputable def pureCloseIterConstruction : PR.Construction V closeIterBlueprint where
  zero p := p 0
  succ _ _ previous := ^∀ (pureFormulaCloseConstruction.result SourceL 0 previous)
  zero_defined := .mk fun e => by simp [closeIterBlueprint,sourceQVecZeroDef]
  succ_defined := .mk fun e => by
    simp [closeIterBlueprint,closeOneStepDef,pureFormulaCloseConstruction.result_defined.defined]

noncomputable def pureModelClose (n p : V) : V :=
  (pureCloseIterConstruction (V := V)).result ![p] n

theorem pureModelClose_defined : 𝚺₁-Function₂ (pureModelClose : V → V → V) via closeIterBlueprint.resultDef := by
  refine .mk fun v => ?_
  have h := (pureCloseIterConstruction (V := V)).result_defined.defined v
  simpa [pureModelClose, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using h

#print axioms pureModelClose_defined
#print axioms pureBindPairGraph_iff
#print axioms pureBindTermGraph_iff
end generic
end PA194BindSource
