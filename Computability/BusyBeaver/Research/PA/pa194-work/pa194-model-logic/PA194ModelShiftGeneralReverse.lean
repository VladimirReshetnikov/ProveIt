import PA194ModelAllShiftGeneral
import PA194ModelShiftSameGeneral
import PA194ModelSeedEnvironment
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
local instance shiftReverseGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance shiftReverseGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance shiftReverseGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance shiftReverseGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance shiftReverseGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance shiftReverseGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem shiftRule_generalBaseSlack (e d q : M)
    (hq : q ∈ fstIdx d)
    (ha : RankedAdmission e (shiftRule (setShift SourceL (fstIdx d)) d)) :
    simBase e+q+2 < simReserve e := by
  have hqd : q < d := lt_of_lt_of_le (lt_of_mem hq) (fstIdx_le_self d)
  have hds : d < shiftRule (setShift SourceL (fstIdx d)) d := d_lt_shiftRule _ _
  have hq1 : q+1 ≤ d := lt_iff_succ_le.mp hqd
  have hd1 : d+1 ≤ shiftRule (setShift SourceL (fstIdx d)) d := lt_iff_succ_le.mp hds
  have hq2 : q+2 ≤ shiftRule (setShift SourceL (fstIdx d)) d := by
    have hh := add_le_add_right hq1 1
    have he : q+2 = (q+1)+1 := by norm_num [add_assoc]
    rw [he]
    exact le_trans (by simpa only [add_comm] using hh) hd1
  have hl : q+2 < shiftRule (setShift SourceL (fstIdx d)) d+1 :=
    lt_of_le_of_lt hq2 (lt_add_one _)
  have hh := add_lt_add_right hl (simBase e)
  have hl' : simBase e+q+2 < simBase e+(shiftRule (setShift SourceL (fstIdx d)) d+1) := by
    simpa only [add_assoc,add_comm,add_left_comm] using hh
  exact lt_of_lt_of_le hl' ha.2

theorem simRuleShift_generalSeed_valid (reserve e d q : M)
    (ha : SeedAdmission 0 reserve e (shiftRule (setShift SourceL (fstIdx d)) d))
    (hq : q ∈ fstIdx d) (hp : IsUFormula SourceL q) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (shift SourceL q))
      (numericalTranslation.tr (simPopFree e) q)) := by
  have hi := simPushFree_pop_of_linear e ha.1.1 (depthAdmission_nonempty e _ ha.1)
  have hc := depthAdmission_shift e (setShift SourceL (fstIdx d)) d ha.1
  have hr := depthAdmission_ranked (simPopFree e) d hc
  obtain ⟨hb,hf,hbase,hreserve⟩ := simPushFree_fields (simPopFree e)
  rw [hi] at hb hf hbase hreserve
  have hzero : simBound (simPopFree e) = 0 := by rw [← hb]; exact ha.2.2.1
  have hpos : (0 : M) < simBase (simPopFree e) :=
    lt_of_le_of_lt zero_le (rankedEnvironment_free_lt _ 0 hr.1)
  have hinit : ∀ i ≤ q, (simBound (simPopFree e)).[i] < simBase (simPopFree e) := by
    intro i _; rw [hzero]; simpa using hpos
  have hfree : ∀ i ≤ q, (simFree (simPopFree e)).[i] < simBase (simPopFree e) := by
    intro i _; exact rankedEnvironment_free_lt _ i hr.1
  have hs := shiftRule_generalBaseSlack e d q hq (depthAdmission_ranked e _ ha.1)
  have hbudget : simBase (simPopFree e)+q+2 < simReserve (simPopFree e) := by
    rw [hreserve] at hs
    rw [hbase] at hs
    have hh : simBase (simPopFree e)+q+2 ≤ (simBase (simPopFree e)+1)+q+2 := by
      have hh1 := add_le_add_right (le_of_lt (lt_add_one (simBase (simPopFree e)))) (q+2)
      simpa only [add_assoc,add_comm,add_left_comm] using hh1
    exact lt_of_le_of_lt hh hs
  have hshift := generalBaseShift_all_codes q (simBound (simPopFree e)) (simFree (simPopFree e))
    (simBase (simPopFree e)) (simReserve (simPopFree e)) hp hinit hfree hbudget
  have hsame := shift_translation_sameBase q (simBound (simPopFree e)) (simFree (simPopFree e))
    (simBase (simPopFree e)) (simBase (simPopFree e)+1) (simReserve (simPopFree e)) hp
  have hresult : numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr (simPushFree (simPopFree e)) (shift SourceL q))
      (numericalTranslation.tr (simPopFree e) q)) := by
    change TargetProvable (impValue (negatedTranslation (simPushFree (simPopFree e)) (shift SourceL q))
      (negatedTranslation (simPopFree e) q))
    obtain ⟨hb',hf',hbase',hreserve'⟩ := simPushFree_fields (simPopFree e)
    rw [negatedTranslation_any,negatedTranslation_any,hb',hf',hbase',hreserve',hsame]
    exact contrapose hshift.1
  rw [hi] at hresult
  exact hresult

theorem simRuleShift_generalSeed_set (reserve e d q : M)
    (ha : SeedAdmission 0 reserve e (shiftRule (setShift SourceL (fstIdx d)) d))
    (hs : IsFormulaSet SourceL (fstIdx d)) (hq : q ∈ fstIdx d) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (shift SourceL q))
      (numericalTranslation.tr (simPopFree e) q)) :=
  simRuleShift_generalSeed_valid reserve e d q ha hq (hs q hq).isUFormula

#print axioms shiftRule_generalBaseSlack
#print axioms simRuleShift_generalSeed_valid
#print axioms simRuleShift_generalSeed_set
end models
end PA194ModelLogic
