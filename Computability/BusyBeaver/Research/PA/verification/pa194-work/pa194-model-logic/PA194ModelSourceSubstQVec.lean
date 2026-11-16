import PA194ModelSourceQVecHistory
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
local instance sourceSubstQVecZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceSubstQVecOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceSubstQVecAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceSubstQVecMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceSubstQVecLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceSubstQVecIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Every lifted singleton substitution has one slot per crossed binder plus its free slot. -/
theorem sourceSubstQVec_trace_typed (limit s witness : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&witness] : M)] s)
    (hl : limit + 1 = lh s) :
    ∀ i ≤ limit, IsSemitermVec SourceL (i+1) i (znth s i) := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    intro hi
    rw [sourceQVec_trace_start _ s h]
    simp
  | succ i ih =>
    intro hi
    have hlt : i < limit := lt_iff_succ_le.mpr hi
    have hi' : i ≤ limit := le_trans le_self_add hi
    rw [sourceQVec_trace_step _ limit s i h hl hlt]
    simpa only [add_assoc] using (ih hi').qVec

/-- The lifted substitution fixes all inner bound variables and substitutes the original one by the chosen free variable. -/
theorem sourceSubstQVec_trace_entries (limit s witness : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&witness] : M)] s)
    (hl : limit + 1 = lh s) :
    ∀ i ≤ limit, (∀ j < i, (znth s i).[j] = ^#j) ∧ (znth s i).[i] = ^&witness := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    rw [sourceQVec_trace_start _ s h]
    simp
  | succ i ih =>
    intro hi
    have hlt : i < limit := lt_iff_succ_le.mpr hi
    have hi' : i ≤ limit := le_trans le_self_add hi
    have hp := ih hi'
    have hty := sourceSubstQVec_trace_typed limit s witness h hl i hi'
    rw [sourceQVec_trace_step _ limit s i h hl hlt]
    constructor
    · intro j hj
      rcases zero_or_succ j with (rfl | ⟨j,rfl⟩)
      · simp [qVec]
      · have hj' : j < i := by simpa using hj
        have hj'' : j < i+1 := lt_trans hj' (lt_add_one i)
        simp [qVec, hty.lh, nth_termBShiftVec hty.isUTerm hj'', hp.1 j hj']
    · have hj : i < i+1 := lt_add_one i
      simp [qVec, hty.lh, nth_termBShiftVec hty.isUTerm hj, hp.2]

#print axioms sourceSubstQVec_trace_entries
#print axioms sourceSubstQVec_trace_typed
end models
end PA194ModelLogic
