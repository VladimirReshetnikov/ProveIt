import PA194GuardedEqualityCancel
import PA194GuardedSymmetryAt
import PA194GuardedTransitivityAt
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open PA194ContextSpecializeCode PA194ContextModusPonensCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance uvarFinalZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance uvarFinalOne : One M := ⟨F oneCode Fin.elim0⟩
local instance uvarFinalAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance uvarFinalMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance uvarFinalLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance uvarFinalIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194ForwardReflProof PA194ClosedEnvironment PA194FormulaDispatcher PA194PAeqBind
noncomputable local instance : adjunctiveFullSepTheory.Δ₁ := adjunctiveFullSepTheoryDelta


theorem fullSource_uVar (i : M) : GDerivable adjunctiveFullSepTheory
    (insert (tr (uniq (^&i))) (∅ : M)) := by
  rw [← singleton_eq_insert]
  apply guarded_uVar_of_symm_trans
  · intro y z
    exact fullSource_pointwise_symmetry y z
  · intro x y z
    exact fullSource_pointwise_transitivity x z y

#print axioms fullSource_uVar
end models
end PA194GuardedCompiler
