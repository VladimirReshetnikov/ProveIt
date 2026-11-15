import PA194ModelBaseFreshGeneral
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
local instance shiftAllGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance shiftAllGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance shiftAllGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance shiftAllGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance shiftAllGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance shiftAllGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- The complete universal-rule shift field for an arbitrary source formula,
under ranked admission and an empty initial bound stack. -/
theorem simRuleAllShift_generalRanked (e s p q d : M)
    (ha : RankedAdmission e (allIntro s p d)) (hb : simBound e = 0)
    (hs : IsFormulaSet SourceL s) (hq : q ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalTranslation.tr (simPushFree e) (shift SourceL q))) := by
  have hpos : (0 : M) < simBase e := lt_of_le_of_lt zero_le (rankedEnvironment_free_lt e 0 ha.1)
  have hinit : ∀ i ≤ q, (simBound e).[i] < simBase e := by
    intro i hi; rw [hb]; simpa using hpos
  have hfree : ∀ i ≤ q, (simFree e).[i] < simBase e := by
    intro i hi; exact rankedEnvironment_free_lt e i ha.1
  have hp := (hs _ hq).isUFormula
  have hshift := generalBaseShift_all_codes q (simBound e) (simFree e) (simBase e) (simReserve e)
    hp hinit hfree (allIntro_generalBaseSlack e s p q d hq ha)
  have hsame := shift_translation_sameBase q (simBound e) (simFree e) (simBase e)
    (simBase e+1) (simReserve e) hp
  change TargetProvable (impValue (negatedTranslation e q)
    (negatedTranslation (simPushFree e) (shift SourceL q)))
  obtain ⟨hbound,hfree',hbase,hreserve⟩ := simPushFree_fields e
  rw [negatedTranslation_any,negatedTranslation_any,hbound,hfree',hbase,hreserve,hsame]
  exact contrapose hshift.2

theorem simRuleAllShift_generalSeed (reserve e s p q d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s p d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s) (hq : q ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalTranslation.tr (simPushFree e) (shift SourceL q))) :=
  simRuleAllShift_generalRanked e s p q d (depthAdmission_ranked e _ ha.1) ha.2.2.1 hs hq

#print axioms simRuleAllShift_generalRanked
#print axioms simRuleAllShift_generalSeed
end models
end PA194ModelLogic
