import PA194ModelSourceSubstStack
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
local instance sourceSubstTermZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceSubstTermOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceSubstTermAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceSubstTermMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceSubstTermLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceSubstTermIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






noncomputable def sourceSubstTerm (s k t : M) : M := termSubst SourceL (znth s k) t

theorem sourceSubstTerm_allocated (limit s k t bound free base witness : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&witness] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (ht : IsSemiterm SourceL (k+1) t) :
    F termLabelCode ![sourceSubstTerm s k t,F allocateBound ![k,base,bound],free] =
      F termLabelCode ![t,F allocateBound ![k,base,pair (free.[witness]) bound+1],free] := by
  have he := sourceSubstQVec_trace_entries limit s witness h hl k hk
  have ha := sourceSubstStack_aligned k base (free.[witness]) bound
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨j,hj⟩ | ⟨j,hj⟩
  · subst t
    have hj : j < k+1 := by simpa only [IsSemiterm.bvar] using ht
    have hjle : j ≤ k := by simpa only [le_iff_lt_succ] using hj
    rcases lt_or_eq_of_le hjle with hjlt | rfl
    · have hv : sourceSubstTerm s k (^#j) = ^#j := by simp [sourceSubstTerm,he.1 j hjlt]
      rw [hv,termLabel_bound_nth,termLabel_bound_nth,ha.1 j hjlt]
    · have hv : sourceSubstTerm s j (^#j) = ^&witness := by simp [sourceSubstTerm,he.2]
      rw [hv,termLabel_free_nth,termLabel_bound_nth,ha.2]
  · subst t
    have hv : sourceSubstTerm s k (^&j) = ^&j := by simp [sourceSubstTerm]
    rw [hv,termLabel_free_nth,termLabel_free_nth]

#print axioms sourceSubstTerm_allocated
end models
end PA194ModelLogic
