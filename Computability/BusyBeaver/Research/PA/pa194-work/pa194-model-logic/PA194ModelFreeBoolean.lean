import PA194ModelFreeTerm
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
local instance freeBooleanZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBooleanOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBooleanAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBooleanMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBooleanLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBooleanIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev SourceL := M6.PA.RelationalSource.language

noncomputable def FreeBridge (p bound freeEnv base reserve : M) : Prop :=
  F fixedFormulaTranslation ![LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL p,
      bound,pair base freeEnv+1,base+1,reserve] =
    F fixedFormulaTranslation ![p,pair base bound+1,freeEnv,base+1,reserve]

theorem free_and_code (p q : M) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (p ^⋏ q) =
      LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL p ^⋏
        LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL q := by
  simp only [LO.FirstOrder.Arithmetic.Bootstrapping.free,substs1,shift_and hp hq,
    substs_and hp.shift hq.shift]

theorem free_or_code (p q : M) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (p ^⋎ q) =
      LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL p ^⋎
        LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL q := by
  simp only [LO.FirstOrder.Arithmetic.Bootstrapping.free,substs1,shift_or hp hq,
    substs_or hp.shift hq.shift]

theorem freeBridge_and (p q bound freeEnv base reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hq : IsSemiformula SourceL 1 q)
    (ihp : FreeBridge p bound freeEnv base reserve) (ihq : FreeBridge q bound freeEnv base reserve) :
    FreeBridge (p ^⋏ q) bound freeEnv base reserve := by
  unfold FreeBridge at ihp ihq ⊢
  rw [free_and_code p q hp.isUFormula hq.isUFormula,
    fixedFormulaTranslation_and _ _ _ _ _ _ hp.free.isUFormula hq.free.isUFormula,
    fixedFormulaTranslation_and _ _ _ _ _ _ hp.isUFormula hq.isUFormula,ihp,ihq]

theorem freeBridge_or (p q bound freeEnv base reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hq : IsSemiformula SourceL 1 q)
    (ihp : FreeBridge p bound freeEnv base reserve) (ihq : FreeBridge q bound freeEnv base reserve) :
    FreeBridge (p ^⋎ q) bound freeEnv base reserve := by
  unfold FreeBridge at ihp ihq ⊢
  rw [free_or_code p q hp.isUFormula hq.isUFormula,
    fixedFormulaTranslation_or _ _ _ _ _ _ hp.free.isUFormula hq.free.isUFormula,
    fixedFormulaTranslation_or _ _ _ _ _ _ hp.isUFormula hq.isUFormula,ihp,ihq]

theorem freeBridge_verum (bound freeEnv base reserve : M) :
    FreeBridge (^⊤ : M) bound freeEnv base reserve := by
  unfold FreeBridge
  simp only [LO.FirstOrder.Arithmetic.Bootstrapping.free,substs1,shift_verum,substs_verum]
  rw [fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]

theorem freeBridge_falsum (bound freeEnv base reserve : M) :
    FreeBridge (^⊥ : M) bound freeEnv base reserve := by
  unfold FreeBridge
  simp only [LO.FirstOrder.Arithmetic.Bootstrapping.free,substs1,shift_falsum,substs_falsum]
  rw [fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]

#print axioms free_and_code
#print axioms free_or_code
#print axioms freeBridge_and
#print axioms freeBridge_or
#print axioms freeBridge_verum
#print axioms freeBridge_falsum
end models
end PA194ModelLogic
