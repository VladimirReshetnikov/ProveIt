import PA194ModelSourceSubstQVec
import PA194ModelQuantifierFreeFresh
import PA194ModelSafeQF
import PA194ModelExMembership
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! Internal source substitution at arbitrary binder depth. -/
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
local instance sourceSubstStackZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceSubstStackOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceSubstStackAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceSubstStackMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceSubstStackLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceSubstStackIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






def sourceSubstStackInv (stage₁ stage₂ : M → M) (root k : M) : Prop :=
  (∀ j < k, (stage₁ k).[j] = (stage₂ k).[j]) ∧ (stage₂ k).[k] = root

theorem sourceSubstStackInv_definable (stage₁ stage₂ : M → M) (root : M)
    (h₁ : 𝚺₁-Function₁ stage₁) (h₂ : 𝚺₁-Function₁ stage₂) :
    𝚺₁-Predicate (sourceSubstStackInv stage₁ stage₂ root) := by
  haveI := h₁
  haveI := h₂
  unfold sourceSubstStackInv
  definability

/-- Allocating matching inner binders preserves their labels and the substituted root label. -/
theorem sourceSubstStack_aligned (k allocBase root initial : M) :
    (∀ j < k, (F allocateBound ![k,allocBase,initial]).[j] =
      (F allocateBound ![k,allocBase,pair root initial+1]).[j]) ∧
    (F allocateBound ![k,allocBase,pair root initial+1]).[k] = root := by
  haveI : 𝚺₁-Function₁ (fun i : M => F allocateBound ![i,allocBase,initial]) :=
    PA194CodeInstance.unary_of_three allocateBound (allocBase) initial
  haveI : 𝚺₁-Function₁ (fun i : M => F allocateBound ![i,allocBase,pair root initial+1]) :=
    PA194CodeInstance.unary_of_three allocateBound (allocBase) (pair root initial+1)
  have hdef := sourceSubstStackInv_definable
    (fun i : M => F allocateBound ![i,allocBase,initial])
    (fun i : M => F allocateBound ![i,allocBase,pair root initial+1]) root inferInstance inferInstance
  change sourceSubstStackInv (fun i : M => F allocateBound ![i,allocBase,initial])
    (fun i : M => F allocateBound ![i,allocBase,pair root initial+1]) root k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero =>
    unfold sourceSubstStackInv
    dsimp only
    rw [allocateBound_zero,allocateBound_zero]
    simp [←adjoin_def]
  | succ k ih =>
    unfold sourceSubstStackInv at ih ⊢
    dsimp only at ih ⊢
    rw [allocateBound_succ,allocateBound_succ]
    constructor
    · intro j hj
      rcases zero_or_succ j with (rfl | ⟨j,rfl⟩)
      · simp [←adjoin_def]
      · have hj' : j < k := by simpa using hj
        simpa [←adjoin_def] using ih.1 j hj'
    · simpa [←adjoin_def] using ih.2

#print axioms sourceSubstStack_aligned
end models
end PA194ModelLogic
