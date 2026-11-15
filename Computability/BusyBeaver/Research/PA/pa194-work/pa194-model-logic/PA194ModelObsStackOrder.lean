import PA194ModelObsGeneral
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
local instance obsStackOrderZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance obsStackOrderOne : One M := ⟨F oneCode Fin.elim0⟩
local instance obsStackOrderAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance obsStackOrderMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance obsStackOrderLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance obsStackOrderIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






def stageBeforeCurrent (stage : M → M) (ceiling base n : M) : Prop :=
  ∀ i ≤ ceiling, (stage n).[i] < base+n

theorem stageBeforeCurrent_definable (stage : M → M) (ceiling base : M)
    (hs : 𝚺₁-Function₁ stage) : 𝚺₁-Predicate (stageBeforeCurrent stage ceiling base) := by
  haveI := hs
  unfold stageBeforeCurrent
  definability

theorem allocatedBound_beforeCurrent (ceiling base initial n : M)
    (hinit : ∀ i ≤ ceiling, initial.[i] < base) (hn : n ≤ ceiling) :
    ∀ i ≤ ceiling, (F allocateBound ![n,base,initial]).[i] < base+n := by
  let stage : M → M := fun n => F allocateBound ![n,base,initial]
  haveI : 𝚺₁-Predicate (stageBeforeCurrent stage ceiling base) :=
    stageBeforeCurrent_definable stage ceiling base (PA194CodeInstance.unary_of_three allocateBound base initial)
  have hdef : 𝚺₁-Predicate (fun n : M => n ≤ ceiling → stageBeforeCurrent stage ceiling base n) := by definability
  have hall : ∀ n : M, n ≤ ceiling → stageBeforeCurrent stage ceiling base n := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _ i hi
      change (F allocateBound ![0,base,initial]).[i] < base+0
      rw [allocateBound_zero,add_zero]
      exact hinit i hi
    case succ n ih =>
      intro hn i hi
      have hn' : n ≤ ceiling := le_trans (le_of_lt (lt_add_one n)) hn
      change (F allocateBound ![n+1,base,initial]).[i] < base+(n+1)
      rw [allocateBound_succ]
      rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
      · rw [nth_zero]
        have hh : base+n < base+(n+1) := by
          have := lt_add_one (base+n)
          simpa only [add_assoc] using this
        simpa [fstIdx] using hh
      · rw [nth_succ]
        have hj : j ≤ ceiling := le_trans (le_of_lt (lt_add_one j)) hi
        have hp := ih hn' j hj
        change (F allocateBound ![n,base,initial]).[j] < base+n at hp
        have hh : base+n < base+(n+1) := by
          have := lt_add_one (base+n)
          simpa only [add_assoc] using this
        simpa [sndIdx] using lt_trans hp hh
  exact hall n hn

#print axioms stageBeforeCurrent_definable
#print axioms allocatedBound_beforeCurrent
end models
end PA194ModelLogic
