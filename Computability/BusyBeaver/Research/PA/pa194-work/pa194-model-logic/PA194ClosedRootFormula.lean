import PA194RootFormula
import PA194UniformFullyClosed
import PA194UniformCloseModel
import PA194FreeBoundClosed
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def closedRootFormula (p : V) : V :=
  pureModelClose (pureFormulaFreeBound (rootFormula p)) (rootFormula p)
noncomputable def closedRootFormulaGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ q n, !rootFormulaGraph q p ∧ !pureFormulaFreeBoundGraph n q ∧ !closeIterBlueprint.resultDef out n q”
theorem closedRootFormula_defined : 𝚺₁-Function₁ (closedRootFormula : V → V) via closedRootFormulaGraph := by
  haveI : 𝚺₁-Function₁ (pureFormulaFreeBound : V → V) via pureFormulaFreeBoundGraph := pureFormulaFreeBound_defined
  haveI : 𝚺₁-Function₂ (pureModelClose : V → V → V) via closeIterBlueprint.resultDef := pureModelClose_defined
  refine .mk fun v => ?_
  simp [closedRootFormulaGraph,closedRootFormula]
end generic
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance closedRootZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance closedRootOne : One M := ⟨F oneCode Fin.elim0⟩
local instance closedRootAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance closedRootMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance closedRootLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance closedRootIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem closedRootFormula_sentence {p : M} (hp : IsSemiformula PA194PAeq.language 0 p) :
    IsSemiformula SourceL 0 (closedRootFormula p) ∧ shift SourceL (closedRootFormula p) = closedRootFormula p := by
  rw [closedRootFormula,pureFormulaFreeBound_model,pureModelClose_model]
  exact modelClose_FVFree _ _ (rootFormula_valid hp) (le_refl _)
theorem closedRootFormula_falsum : closedRootFormula (^⊥ : M) = ^⊥ := by
  rw [closedRootFormula,rootFormula_falsum,pureFormulaFreeBound_model,formulaFreeBound_falsum,pureModelClose_model,modelClose_zero]
#print axioms closedRootFormula_defined
#print axioms closedRootFormula_sentence
#print axioms closedRootFormula_falsum
end models
end PA194FormulaDispatcher
