import PA194TermFreeBound
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
local instance freeBoundFormulaZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundFormulaOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundFormulaAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundFormulaMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundFormulaLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundFormulaIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Largest free index plus one in the two arguments of a source relation. -/
noncomputable def pairFreeBound (v : M) : M := max (termFreeBound v.[0]) (termFreeBound v.[1])

def pairFreeBoundGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y v. ∃ a, !nthDef a v 0 ∧ ∃ b, !nthDef b v 1 ∧
    ∃ aa, !termFreeBoundGraph aa a ∧ ∃ bb, !termFreeBoundGraph bb b ∧ !max.dfn y aa bb”

instance pairFreeBound_defined : 𝚺₁-Function₁ (pairFreeBound : M → M) via pairFreeBoundGraph := .mk fun v ↦ by
  simp [pairFreeBoundGraph,pairFreeBound]

namespace FormulaFreeBound
noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. !pairFreeBoundGraph y v”
  nrel := .mkSigma “y param k R v. !pairFreeBoundGraph y v”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. y = y₁”
  exs := .mkSigma “y param p₁ y₁. y = y₁”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”

noncomputable def construction : UformulaRec1.Construction M blueprint where
  rel := fun _ _ _ v ↦ pairFreeBound v
  nrel := fun _ _ _ v ↦ pairFreeBound v
  verum := fun _ ↦ 0
  falsum := fun _ ↦ 0
  and := fun _ _ _ y₁ y₂ ↦ max y₁ y₂
  or := fun _ _ _ y₁ y₂ ↦ max y₁ y₂
  all := fun _ _ y₁ ↦ y₁
  exs := fun _ _ y₁ ↦ y₁
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
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
end FormulaFreeBound

noncomputable def formulaFreeBound (p : M) : M := FormulaFreeBound.construction.result SourceL 0 p

theorem formulaFreeBound_definable : 𝚺₁-Function₁ (formulaFreeBound : M → M) := by
  unfold formulaFreeBound
  definability

theorem formulaFreeBound_rel (k r v : M) (hr : SourceL.IsRel k r) (hv : IsUTermVec SourceL k v) :
    formulaFreeBound (^rel k r v) = pairFreeBound v := by
  simp [formulaFreeBound,FormulaFreeBound.construction,hr,hv]
theorem formulaFreeBound_nrel (k r v : M) (hr : SourceL.IsRel k r) (hv : IsUTermVec SourceL k v) :
    formulaFreeBound (^nrel k r v) = pairFreeBound v := by
  simp [formulaFreeBound,FormulaFreeBound.construction,hr,hv]
theorem formulaFreeBound_verum : formulaFreeBound (^⊤ : M) = 0 := by
  simp [formulaFreeBound,FormulaFreeBound.construction]
theorem formulaFreeBound_falsum : formulaFreeBound (^⊥ : M) = 0 := by
  simp [formulaFreeBound,FormulaFreeBound.construction]
theorem formulaFreeBound_and (p q : M) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    formulaFreeBound (p ^⋏ q) = max (formulaFreeBound p) (formulaFreeBound q) := by
  simp [formulaFreeBound,FormulaFreeBound.construction,hp,hq]
theorem formulaFreeBound_or (p q : M) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    formulaFreeBound (p ^⋎ q) = max (formulaFreeBound p) (formulaFreeBound q) := by
  simp [formulaFreeBound,FormulaFreeBound.construction,hp,hq]
theorem formulaFreeBound_all (p : M) (hp : IsUFormula SourceL p) :
    formulaFreeBound (^∀ p) = formulaFreeBound p := by
  simp [formulaFreeBound,FormulaFreeBound.construction,hp]
theorem formulaFreeBound_ex (p : M) (hp : IsUFormula SourceL p) :
    formulaFreeBound (^∃ p) = formulaFreeBound p := by
  simp [formulaFreeBound,FormulaFreeBound.construction,hp]

#print axioms formulaFreeBound_definable
#print axioms formulaFreeBound_rel
#print axioms formulaFreeBound_all
end models
end PA194BindSource
