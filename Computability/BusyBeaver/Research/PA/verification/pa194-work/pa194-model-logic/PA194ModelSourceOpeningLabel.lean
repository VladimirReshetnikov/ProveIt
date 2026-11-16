import PA194ModelSourceQVecTyped
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
local instance sourceOpeningLabelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceOpeningLabelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceOpeningLabelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceOpeningLabelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceOpeningLabelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceOpeningLabelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Opening a term under `k` binders, using the model-internal lifted-vector history. -/
noncomputable def sourceOpeningTerm (s k t : M) : M :=
  termSubst SourceL (znth s k) (termShift SourceL t)

theorem sourceOpeningTerm_label (limit s k t before after free root : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (ht : IsSemiterm SourceL (k+1) t)
    (halign : ∀ j < k, after.[j] = before.[j])
    (hroot : before.[k] = root) :
    F termLabelCode ![sourceOpeningTerm s k t,after,pair root free+1] =
      F termLabelCode ![t,before,free] := by
  have he := sourceQVec_trace_entries limit s h hl k hk
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨j,hj⟩ | ⟨j,hj⟩
  · subst t
    have hj : j < k+1 := by simpa only [IsSemiterm.bvar] using ht
    have hjle : j ≤ k := by simpa only [le_iff_lt_succ] using hj
    rcases lt_or_eq_of_le hjle with hjlt | rfl
    · have hv : sourceOpeningTerm s k (^#j) = ^#j := by
        simp [sourceOpeningTerm,he.1 j hjlt]
      rw [hv,termLabel_bound_nth,termLabel_bound_nth,halign j hjlt]
    · have hv : sourceOpeningTerm s j (^#j) = ^&(0 : M) := by
        simp [sourceOpeningTerm,he.2]
      rw [hv,termLabel_free_nth,termLabel_bound_nth,hroot]
      simp [←adjoin_def]
  · subst t
    have hv : sourceOpeningTerm s k (^&j) = ^&(j+1) := by simp [sourceOpeningTerm]
    rw [hv,termLabel_free_nth,termLabel_free_nth]
    simp [←adjoin_def]

#print axioms sourceOpeningTerm_label
end models
end PA194ModelLogic
