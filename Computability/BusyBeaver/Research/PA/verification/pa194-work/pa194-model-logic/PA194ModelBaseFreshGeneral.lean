import PA194ModelBaseShiftGeneral
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
local instance baseFreshGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance baseFreshGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance baseFreshGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance baseFreshGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance baseFreshGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance baseFreshGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- The actual universal-rule node provides enough reserve for the general
base-shift induction on every member of its source sequent. -/
theorem allIntro_generalBaseSlack (e s p q d : M)
    (hq : q ∈ s) (ha : RankedAdmission e (allIntro s p d)) :
    simBase e+q+2 < simReserve e := by
  have hqs : q < s := lt_of_mem hq
  have hsd : s < allIntro s p d := seq_lt_allIntro s p d
  have hq1 : q+1 ≤ s := lt_iff_succ_le.mp hqs
  have hs1 : s+1 ≤ allIntro s p d := lt_iff_succ_le.mp hsd
  have hq2 : q+2 ≤ allIntro s p d := by
    have hh := add_le_add_right hq1 1
    have he : q+2 = (q+1)+1 := by norm_num [add_assoc]
    rw [he]
    exact le_trans (by simpa only [add_comm] using hh) hs1
  have hl : q+2 < allIntro s p d+1 := lt_of_le_of_lt hq2 (lt_add_one _)
  have hh := add_lt_add_right hl (simBase e)
  have hl' : simBase e+q+2 < simBase e+(allIntro s p d+1) := by
    simpa only [add_assoc,add_comm,add_left_comm] using hh
  exact lt_of_lt_of_le hl' ha.2

/-- The complete universal eigenlabel-freshness field for an arbitrary
internally valid source-sequent member, under ranked admission and an empty
initial bound stack. -/
theorem simRuleAllFresh_generalRanked (e s p q d : M)
    (ha : RankedAdmission e (allIntro s p d)) (hb : simBound e = 0)
    (hs : IsFormulaSet SourceL s) (hq : q ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalQuant.all (simBase e) (numericalTranslation.tr e q))) := by
  have hpos : (0 : M) < simBase e := lt_of_le_of_lt zero_le (rankedEnvironment_free_lt e 0 ha.1)
  have hinit : ∀ i ≤ q, (simBound e).[i] < simBase e := by
    intro i hi
    rw [hb]
    simpa using hpos
  have hfree : ∀ i ≤ q, (simFree e).[i] < simBase e := by
    intro i hi
    exact rankedEnvironment_free_lt e i ha.1
  have hshift := generalBaseShift_all_codes q (simBound e) (simFree e) (simBase e) (simReserve e)
    (hs _ hq).isUFormula hinit hfree (allIntro_generalBaseSlack e s p q d hq ha)
  exact simRuleAllFresh_of_baseShift e s q _ hs hq ha hb hshift.1 hshift.2

/-- The exact `CutValidity.Sim.ruleAllFresh` field under the actual seeded
admission invariant, with no restriction on source formula shape. -/
theorem simRuleAllFresh_generalSeed (reserve e s p q d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s p d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s) (hq : q ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalQuant.all (simBase e) (numericalTranslation.tr e q))) :=
  simRuleAllFresh_generalRanked e s p q d (depthAdmission_ranked e _ ha.1) ha.2.2.1 hs hq

#print axioms allIntro_generalBaseSlack
#print axioms simRuleAllFresh_generalRanked
#print axioms simRuleAllFresh_generalSeed
end models
end PA194ModelLogic
