import PA194ModelSourceOpeningLabel
import PA194ModelQuantifierFreeFresh
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
local instance sourceOpeningStackZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceOpeningStackOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceOpeningStackAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceOpeningStackMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceOpeningStackLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceOpeningStackIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






def sourceOpeningStackInv (stage₁ stage₂ : M → M) (root k : M) : Prop :=
  (∀ j < k, (stage₁ k).[j] = (stage₂ k).[j]) ∧ (stage₂ k).[k] = root

theorem sourceOpeningStackInv_definable (stage₁ stage₂ : M → M) (root : M)
    (h₁ : 𝚺₁-Function₁ stage₁) (h₂ : 𝚺₁-Function₁ stage₂) :
    𝚺₁-Predicate (sourceOpeningStackInv stage₁ stage₂ root) := by
  haveI := h₁
  haveI := h₂
  unfold sourceOpeningStackInv
  definability

/-- Allocating matching inner binders preserves their labels and the opened root label. -/
theorem sourceOpeningStack_aligned (k base initial : M) :
    (∀ j < k, (F allocateBound ![k,base+1,initial]).[j] =
      (F allocateBound ![k,base+1,pair base initial+1]).[j]) ∧
    (F allocateBound ![k,base+1,pair base initial+1]).[k] = base := by
  haveI : 𝚺₁-Function₁ (fun i : M => F allocateBound ![i,base+1,initial]) :=
    PA194CodeInstance.unary_of_three allocateBound (base+1) initial
  haveI : 𝚺₁-Function₁ (fun i : M => F allocateBound ![i,base+1,pair base initial+1]) :=
    PA194CodeInstance.unary_of_three allocateBound (base+1) (pair base initial+1)
  have hdef := sourceOpeningStackInv_definable
    (fun i : M => F allocateBound ![i,base+1,initial])
    (fun i : M => F allocateBound ![i,base+1,pair base initial+1]) base inferInstance inferInstance
  change sourceOpeningStackInv (fun i : M => F allocateBound ![i,base+1,initial])
    (fun i : M => F allocateBound ![i,base+1,pair base initial+1]) base k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero =>
    unfold sourceOpeningStackInv
    dsimp only
    rw [allocateBound_zero,allocateBound_zero]
    simp [←adjoin_def]
  | succ k ih =>
    unfold sourceOpeningStackInv at ih ⊢
    dsimp only at ih ⊢
    rw [allocateBound_succ,allocateBound_succ]
    constructor
    · intro j hj
      rcases zero_or_succ j with (rfl | ⟨j,rfl⟩)
      · simp [←adjoin_def]
      · have hj' : j < k := by simpa using hj
        simpa [←adjoin_def] using ih.1 j hj'
    · simpa [←adjoin_def] using ih.2

theorem sourceOpeningTerm_allocated (limit s k t bound free base : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (ht : IsSemiterm SourceL (k+1) t) :
    F termLabelCode ![sourceOpeningTerm s k t,F allocateBound ![k,base+1,bound],pair base free+1] =
      F termLabelCode ![t,F allocateBound ![k,base+1,pair base bound+1],free] := by
  have ha := sourceOpeningStack_aligned k base bound
  exact sourceOpeningTerm_label limit s k t _ _ free base h hl hk ht ha.1 ha.2

#print axioms sourceOpeningTerm_allocated
#print axioms sourceOpeningStack_aligned
end models
end PA194ModelLogic
