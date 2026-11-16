import PA194PushHistory
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
local instance repeatModelDefZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance repeatModelDefOne : One M := ⟨F oneCode Fin.elim0⟩
local instance repeatModelDefAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance repeatModelDefMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance repeatModelDefLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance repeatModelDefIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem modelClose_definable : 𝚺₁-Function₂ (modelClose : M → M → M) := by
  change 𝚺₁.Definable (fun v : Fin 3 → M => v 0 = modelClose (v 1) (v 2))
  simpa [modelClose, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    (closeIterConstruction (M := M)).result_defined.to_definable

theorem modelPush_definable : 𝚺₁-Function₂ (modelPush : M → M → M) := by
  change 𝚺₁.Definable (fun v : Fin 3 → M => v 0 = modelPush (v 1) (v 2))
  simpa [modelPush, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    (pushIterConstruction (M := M)).result_defined.to_definable

#print axioms modelClose_definable
#print axioms modelPush_definable
end models
end PA194BindSource
