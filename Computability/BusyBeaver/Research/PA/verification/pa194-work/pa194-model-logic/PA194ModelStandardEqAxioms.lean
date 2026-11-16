import PA194ModelEqRelExt
import PA194ModelRelExtRootBound
import PA194ModelFormulaTranslation
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance eqAxiomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqAxiomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqAxiomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqAxiomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqAxiomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqAxiomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageEqAxiom : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

theorem standardEqAxiom_target (initial free base reserve : M)
    (σ : Sentence M6.PA.RelationalSource.language) (hσ : σ ∈ Theory.eqAxiom M6.PA.RelationalSource.language)
    (hz : base + (⌜σ⌝ : M) ≤ reserve) :
    TargetProvable (F fixedFormulaTranslation ![(⌜σ⌝ : M),initial,free,base,reserve]) := by
  cases hσ with
  | refl => exact fixedFormulaTranslation_eqRefl_target initial free base reserve
  | symm => exact fixedFormulaTranslation_eqSymm_target initial free base reserve
  | trans => exact fixedFormulaTranslation_eqTrans_target initial free base reserve
  | funcExt f => nomatch f
  | relExt r =>
    cases r with
    | eq => exact fixedFormulaTranslation_eqRelExt_target initial free base reserve
    | mem => exact fixedFormulaTranslation_relExt_target_rootBound initial free base reserve hz

#print axioms standardEqAxiom_target
end models
end PA194ModelLogic
