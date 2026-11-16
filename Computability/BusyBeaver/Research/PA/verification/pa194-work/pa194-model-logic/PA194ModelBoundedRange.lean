import PA194ModelLinearSeed
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Deep linear-stack seeds and a depth-indexed partial compiler admission. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
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
local instance boundedRangeZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundedRangeOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundedRangeAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundedRangeMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundedRangeLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundedRangeIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]



/-- Every model-valued initial segment of a Σ₁-definable total function has a common bound. -/
theorem sigmaFunction_boundedRange (f : M → M) (hf : 𝚺₁-Function₁ f) (n : M) :
    ∃ B : M, ∀ i ≤ n, f i ≤ B := by
  haveI := hf
  have hp : 𝚺₁-Predicate (fun k : M => ∃ B : M, ∀ i ≤ k, f i ≤ B) := by definability
  induction n using ISigma1.sigma1_succ_induction
  · exact hp
  case zero =>
    refine ⟨f 0,?_⟩
    intro i hi
    have hi0 : i = 0 := le_antisymm hi zero_le
    rw [hi0]
  case succ n ih =>
    obtain ⟨B,hB⟩ := ih
    refine ⟨B+f (n+1),?_⟩
    intro i hi
    by_cases hin : i ≤ n
    · exact le_trans (hB i hin) (by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ f (n+1)) B
        simpa only [add_zero,zero_add,add_comm] using hh)
    · have hi' : i = n+1 := le_antisymm hi (succ_le_iff_lt.mpr (lt_of_not_ge hin))
      rw [hi']
      have hh := add_le_add_right (zero_le : (0 : M) ≤ B) (f (n+1))
      simpa only [add_zero,zero_add,add_comm] using hh

theorem linearSeed_function_definable (bound reserve : M) :
    𝚺₁-Function₁ (fun n : M => linearSeed bound reserve n) := by
  let stage : M → M := fun n => F allocateBound ![n,1,0]
  haveI : 𝚺₁-Function₁ stage := PA194CodeInstance.unary_of_three allocateBound 1 0
  have hp : 𝚺₁-Function₁ (fun n : M => pair bound (pair (stage n) (pair (n+1) reserve))) := by
    definability
  simpa only [linearSeed,stage] using hp

theorem linearSeed_boundedRange (bound reserve cap : M) :
    ∃ B : M, ∀ n ≤ cap, linearSeed bound reserve n ≤ B :=
  sigmaFunction_boundedRange _ (linearSeed_function_definable bound reserve) cap

#print axioms sigmaFunction_boundedRange
#print axioms linearSeed_function_definable
#print axioms linearSeed_boundedRange
end models
end PA194ModelLogic
