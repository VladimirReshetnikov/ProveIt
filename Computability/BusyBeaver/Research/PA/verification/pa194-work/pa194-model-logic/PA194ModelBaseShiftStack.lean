import PA194ModelBaseShiftDefs
import PA194ModelSafeQF
import PA194ModelExMembership
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! Internal structural induction for arbitrary-label vacuity. -/
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
local instance baseShiftStackZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance baseShiftStackOne : One M := ⟨F oneCode Fin.elim0⟩
local instance baseShiftStackAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance baseShiftStackMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance baseShiftStackLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance baseShiftStackIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem pushLabels_aligned (x y stack ceiling : M) :
    ∀ i ≤ ceiling, LabelAligned x y (pair x stack+1).[i] (pair y stack+1).[i] := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j,rfl⟩
  · rw [←adjoin_def,←adjoin_def,nth_adjoin_zero,nth_adjoin_zero]
    exact Or.inr ⟨rfl,rfl⟩
  · rw [←adjoin_def,←adjoin_def,nth_adjoin_succ,nth_adjoin_succ]
    exact Or.inl rfl

theorem pushLabels_below (head stack ceiling reserve : M)
    (hh : head < reserve) (hs : ∀ i ≤ ceiling, stack.[i] < reserve) :
    ∀ i ≤ ceiling, (pair head stack+1).[i] < reserve := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j,rfl⟩
  · rw [←adjoin_def,nth_adjoin_zero]
    exact hh
  · rw [←adjoin_def,nth_adjoin_succ]
    exact hs j (le_trans (le_of_lt (lt_add_one j)) hi)

theorem pushLabels_avoid (head stack ceiling x : M)
    (hh : head ≠ x) (hs : ∀ i ≤ ceiling, stack.[i] ≠ x) :
    ∀ i ≤ ceiling, (pair head stack+1).[i] ≠ x := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j,rfl⟩
  · rw [←adjoin_def,nth_adjoin_zero]
    exact hh
  · rw [←adjoin_def,nth_adjoin_succ]
    exact hs j (le_trans (le_of_lt (lt_add_one j)) hi)

#print axioms pushLabels_aligned
#print axioms pushLabels_below
#print axioms pushLabels_avoid
end models
end PA194ModelLogic
