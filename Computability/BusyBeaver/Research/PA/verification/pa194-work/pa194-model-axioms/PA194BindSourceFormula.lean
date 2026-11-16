import PA194BindPairGraph
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance bindFormulaZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance bindFormulaOne : One M := ⟨F oneCode Fin.elim0⟩
local instance bindFormulaAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance bindFormulaMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance bindFormulaLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance bindFormulaIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance bindPair_defined : 𝚺₁-Function₂ (bindPair : M → M → M) via bindPairGraph := .mk fun v ↦ by
  change bindPairGraph.val.Eval v Empty.elim ↔ v 0 = bindPair (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using (bindPairGraph_iff (v 0) (v 1) (v 2))

namespace FormulaClose
noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ v', !bindPairGraph v' param v ∧ !qqRelDef y k R v'”
  nrel := .mkSigma “y param k R v. ∃ v', !bindPairGraph v' param v ∧ !qqNRelDef y k R v'”
  verum := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  exs := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  allChanges := .mkSigma “param' param. param' = param + 1”
  exsChanges := .mkSigma “param' param. param' = param + 1”

noncomputable def construction : UformulaRec1.Construction M blueprint where
  rel := fun depth k R v ↦ ^rel k R (bindPair depth v)
  nrel := fun depth k R v ↦ ^nrel k R (bindPair depth v)
  verum := fun _ ↦ ^⊤
  falsum := fun _ ↦ ^⊥
  and := fun _ _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or := fun _ _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all := fun _ _ y₁ ↦ ^∀ y₁
  exs := fun _ _ y₁ ↦ ^∃ y₁
  allChanges := fun depth ↦ depth+1
  exsChanges := fun depth ↦ depth+1
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]
end FormulaClose

noncomputable def bindFormula (depth p : M) : M :=
  FormulaClose.construction.result SourceL depth p

theorem bindFormula_definable : 𝚺₁-Function₂ (bindFormula : M → M → M) := by
  unfold bindFormula
  definability
theorem bindFormula_rel (d k r v : M) (hr : SourceL.IsRel k r)
    (hv : IsUTermVec SourceL k v) :
    bindFormula d (^rel k r v) = ^rel k r (bindPair d v) := by
  simp [bindFormula, FormulaClose.construction, hr, hv]
theorem bindFormula_nrel (d k r v : M) (hr : SourceL.IsRel k r)
    (hv : IsUTermVec SourceL k v) :
    bindFormula d (^nrel k r v) = ^nrel k r (bindPair d v) := by
  simp [bindFormula, FormulaClose.construction, hr, hv]
theorem bindFormula_verum (d : M) : bindFormula d (^⊤ : M) = ^⊤ := by
  simp [bindFormula, FormulaClose.construction]
theorem bindFormula_falsum (d : M) : bindFormula d (^⊥ : M) = ^⊥ := by
  simp [bindFormula, FormulaClose.construction]
theorem bindFormula_and (d p q : M) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    bindFormula d (p ^⋏ q) = bindFormula d p ^⋏ bindFormula d q := by
  simp [bindFormula, FormulaClose.construction, hp, hq]
theorem bindFormula_or (d p q : M) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    bindFormula d (p ^⋎ q) = bindFormula d p ^⋎ bindFormula d q := by
  simp [bindFormula, FormulaClose.construction, hp, hq]
theorem bindFormula_all (d p : M) (hp : IsUFormula SourceL p) :
    bindFormula d (^∀ p) = ^∀ (bindFormula (d+1) p) := by
  simp [bindFormula, FormulaClose.construction, hp]
theorem bindFormula_ex (d p : M) (hp : IsUFormula SourceL p) :
    bindFormula d (^∃ p) = ^∃ (bindFormula (d+1) p) := by
  simp [bindFormula, FormulaClose.construction, hp]
#print axioms bindFormula_definable
#print axioms bindFormula_rel
#print axioms bindFormula_all
end models
end PA194BindSource
