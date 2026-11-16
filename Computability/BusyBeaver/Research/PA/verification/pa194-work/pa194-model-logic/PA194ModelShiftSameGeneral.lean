import PA194ModelShiftSameAtom
import PA194ModelDepthRules
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
local instance shiftSameInductionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance shiftSameInductionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance shiftSameInductionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance shiftSameInductionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance shiftSameInductionLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance shiftSameInductionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






noncomputable def depthShiftSame (initial free head base reserve p k : M) : Prop :=
  positiveTranslation (depthEnvironment initial (pair head free+1) base reserve k) (shift SourceL p) =
    positiveTranslation (depthEnvironment initial free base reserve k) p

theorem depthShiftSame_definable (initial free head base reserve : M) :
    𝚺₁-Relation (depthShiftSame initial free head base reserve) := by
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₁ (shift SourceL : M → M) := shift.definable
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base,initial]) :=
    PA194CodeInstance.unary_of_three allocateBound base initial
  haveI : 𝚺₁-Function₁ (depthEnvironment initial (pair head free+1) base reserve) := by
    unfold depthEnvironment; definability
  haveI : 𝚺₁-Function₁ (depthEnvironment initial free base reserve) := by
    unfold depthEnvironment; definability
  unfold depthShiftSame
  definability

theorem depthShiftSame_eq (initial free head base reserve p k : M) :
    depthShiftSame initial free head base reserve p k ↔
      F fixedFormulaTranslation ![shift SourceL p,F allocateBound ![k,base,initial],pair head free+1,base+k,reserve] =
        F fixedFormulaTranslation ![p,F allocateBound ![k,base,initial],free,base+k,reserve] := by
  unfold depthShiftSame depthEnvironment
  rw [positiveTranslation_model,positiveTranslation_model]

/-- Source shifting is exactly mirrored by a free-stack push when both
translations allocate binders from the same base, at arbitrary depth. -/
theorem shift_translation_sameBase (p initial free head base reserve : M) (hp : IsUFormula SourceL p) :
    F fixedFormulaTranslation ![shift SourceL p,initial,pair head free+1,base,reserve] =
      F fixedFormulaTranslation ![p,initial,free,base,reserve] := by
  let K := p
  haveI : 𝚺₁-Relation (depthShiftSame initial free head base reserve) :=
    depthShiftSame_definable initial free head base reserve
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ k ≤ K, q+k ≤ K →
      depthShiftSame initial free head base reserve q k) := by definability
  have hall : ∀ q, IsUFormula SourceL q → ∀ k ≤ K, q+k ≤ K →
      depthShiftSame initial free head base reserve q k := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      rw [depthShiftSame_eq]
      exact shift_positiveAtom_sameBase r a b _ free head (base+k) reserve hr ha hb
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      rw [depthShiftSame_eq]
      exact shift_negativeAtom_sameBase r a b _ free head (base+k) reserve hr ha hb
    · intro k hk hbound
      rw [depthShiftSame_eq,shift_verum,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
    · intro k hk hbound
      rw [depthShiftSame_eq,shift_falsum,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA
      have ih2 := ihb k hk hB
      rw [depthShiftSame_eq] at ih1 ih2 ⊢
      rw [shift_and ha hb,fixedFormulaTranslation_and _ _ _ _ _ _ ha.shift hb.shift,
        fixedFormulaTranslation_and _ _ _ _ _ _ ha hb,ih1,ih2]
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA
      have ih2 := ihb k hk hB
      rw [depthShiftSame_eq] at ih1 ih2 ⊢
      rw [shift_or ha hb,fixedFormulaTranslation_or _ _ _ _ _ _ ha.shift hb.shift,
        fixedFormulaTranslation_or _ _ _ _ _ _ ha hb,ih1,ih2]
    · intro a ha ih k hk hbound
      have hle : a+1 ≤ ^∀ a := by
        change a+1 ≤ pair (6 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have ih1 := ih (k+1) hk1 hA
      rw [depthShiftSame_eq] at ih1 ⊢
      rw [shift_all ha,fixedFormulaTranslation_all _ _ _ _ _ ha.shift,
        fixedFormulaTranslation_all _ _ _ _ _ ha]
      rw [allocateBound_succ] at ih1
      have hbaseEq : base+(k+1) = (base+k)+1 := by ac_rfl
      rw [hbaseEq] at ih1
      rw [ih1]
    · intro a ha ih k hk hbound
      have hle : a+1 ≤ ^∃ a := by
        change a+1 ≤ pair (7 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (7 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have ih1 := ih (k+1) hk1 hA
      rw [depthShiftSame_eq] at ih1 ⊢
      rw [shift_exs ha,fixedFormulaTranslation_ex _ _ _ _ _ ha.shift,
        fixedFormulaTranslation_ex _ _ _ _ _ ha]
      rw [allocateBound_succ] at ih1
      have hbaseEq : base+(k+1) = (base+k)+1 := by ac_rfl
      rw [hbaseEq] at ih1
      rw [ih1]
  have h0 := hall p hp 0 (show (0 : M) ≤ K from zero_le) (by simp [K])
  rw [depthShiftSame_eq] at h0
  simpa only [allocateBound_zero,add_zero] using h0

#print axioms depthShiftSame_definable
#print axioms shift_translation_sameBase
end models
end PA194ModelLogic
